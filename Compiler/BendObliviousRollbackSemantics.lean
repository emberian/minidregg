import Compiler.BendObliviousStateSemantics
import Compiler.ObliviousConstantSemantics
import Compiler.BendObliviousMutation

namespace Minidregg.Compiler.BendObliviousStateSemantics
open ObliviousNetwork ObliviousWords ObliviousWordSemantics BendObliviousState
set_option autoImplicit false

theorem WordBound.extends {width : Nat} {first last : Network} {word : Word width}
    (extension : Extension first last) (held : WordBound first word) : WordBound last word :=
  fun bit => extension.bound (held bit)

theorem RowsBound.extends {slots width : Nat} {first last : Network}
    {rows : Vector (Word width) slots} (extension : Extension first last)
    (held : RowsBound first rows) : RowsBound last rows :=
  fun row => WordBound.extends extension (held row)

theorem ControlBound.extends {shape : BendObliviousState.Shape} {first last : Network}
    {value : Control shape} (extension : Extension first last) (held : ControlBound first value) :
    ControlBound last value :=
  ⟨WordBound.extends extension held.tag,
   WordBound.extends extension held.quantity,
   WordBound.extends extension held.failure,
   WordBound.extends extension held.a,
   WordBound.extends extension held.b,
   WordBound.extends extension held.c,
   WordBound.extends extension held.d,
   WordBound.extends extension held.e,
   WordBound.extends extension held.firstLength,
   WordBound.extends extension held.secondLength,
   RowsBound.extends extension held.first,
   RowsBound.extends extension held.second⟩

theorem StateBound.extends {shape : BendObliviousState.Shape} {first last : Network}
    {value : State shape} (extension : Extension first last) (held : StateBound first value) :
    StateBound last value :=
  ⟨RowsBound.extends extension held.heap,
   WordBound.extends extension held.used,
   WordBound.extends extension held.data,
   RowsBound.extends extension held.stack,
   WordBound.extends extension held.stackLength,
   ControlBound.extends extension held.control,
   WordBound.extends extension held.sourceSteps⟩

#assert_axioms WordBound.extends
#assert_axioms RowsBound.extends
#assert_axioms ControlBound.extends
#assert_axioms StateBound.extends
end Minidregg.Compiler.BendObliviousStateSemantics

namespace Minidregg.Compiler.BendObliviousRollbackSemantics
open ObliviousNetwork ObliviousWords ObliviousWordSemantics ObliviousCompositeSemantics
open ObliviousConstantSemantics BendObliviousState BendObliviousStateSemantics BendObliviousMutation
set_option autoImplicit false

/-- Actual finish emits refusal tag 9, then selects the complete original
rollback state on a failed trial. Every heap/cache/frame/counter field is
selected through the proved whole-state builder. Physical material consumption
is deliberately not part of this reversible semantic state. -/
theorem finish_selects {shape : BendObliviousState.Shape} (network : Network)
    (input : Array Bool) (inputShape : input.size = network.inputCount)
    (original : State shape) (trial : Trial shape)
    (originalBound : StateBound network original) (trialBound : StateBound network trial.state)
    (validBound : trial.valid < network.inputCount + network.gates.size)
    (failureBound : WordBound network trial.failure) :
    let tag := (constant 4 9).run network
    let rollback := {original with control := {original.control with tag := tag.1, failure := trial.failure}}
    let result := (finish original trial).run network
    Extension network result.2 ∧
    WordHolds input (fun bit : Fin 4 => (9 : Nat).testBit bit.val) tag.2 tag.1 ∧
    StateRep tag.2 input (if read network input trial.valid then trial.state else rollback)
      result.2 result.1 := by
  let tag := (constant 4 9).run network
  have tagFacts := constant_produces network input inputShape 4 9
  let rollback := {original with control := {original.control with tag := tag.1, failure := trial.failure}}
  have originalAfter := StateBound.extends tagFacts.1 originalBound
  have trialAfter := StateBound.extends tagFacts.1 trialBound
  have rollbackBound : StateBound tag.2 rollback :=
    {originalAfter with control := {originalAfter.control with
      tag := fun bit => (tagFacts.2.2 bit).1,
      failure := WordBound.extends tagFacts.1 failureBound}}
  have selected := muxState_at tag.2 tag.2 input tagFacts.2.1 (Extension.refl tag.2)
    trial.valid trial.state rollback (tagFacts.1.bound validBound) trialAfter rollbackBound
  have retained := tagFacts.1.read input trial.valid inputShape validBound
  rw [retained] at selected
  change Extension network ((muxState trial.valid trial.state rollback).run tag.2).2 ∧
    WordHolds input (fun bit : Fin 4 => (9 : Nat).testBit bit.val) tag.2 tag.1 ∧
    StateRep tag.2 input (if read network input trial.valid then trial.state else rollback)
      ((muxState trial.valid trial.state rollback).run tag.2).2
      ((muxState trial.valid trial.state rollback).run tag.2).1
  exact ⟨tagFacts.1.trans selected.1, tagFacts.2, selected.2⟩

/-- The real accumulated guard preserves the first failure: once valid is
false, later guard reasons cannot replace the retained failure word. While
valid is true it stores this guard's reason, then ANDs its condition. -/
theorem guard_selects {shape : BendObliviousState.Shape} (network : Network)
    (input : Array Bool) (inputShape : input.size = network.inputCount)
    (condition reason : Nat) (trial : Trial shape)
    (validBound : trial.valid < network.inputCount + network.gates.size)
    (conditionBound : condition < network.inputCount + network.gates.size)
    (failureBound : WordBound network trial.failure) :
    let result := (guard condition reason trial).run network
    Extension network result.2 ∧ result.1.state = trial.state ∧
    read result.2 input result.1.valid =
      (read network input trial.valid && read network input condition) ∧
    WordHolds input (fun bit : Fin 5 => if read network input trial.valid then
      reason.testBit bit.val else read network input trial.failure[bit]) result.2 result.1.failure := by
  let error := (constant 5 reason).run network
  have errorFacts := constant_produces network input inputShape 5 reason
  let selected := (mux trial.valid error.1 trial.failure).run error.2
  have selectedFacts := ObliviousVectorSemantics.mux_produces error.2 input errorFacts.2.1
    trial.valid error.1 trial.failure (errorFacts.1.bound validBound)
    (fun bit => (errorFacts.2.2 bit).1) (fun bit => errorFacts.1.bound (failureBound bit))
  have beforeAnd : Extension network selected.2 := errorFacts.1.trans selectedFacts.1
  let valid := (emit (.and trial.valid condition)).run selected.2
  have andExtension := emit_extension selected.2 (.and trial.valid condition)
  have andValue := congrArg (fun value => value.getD false)
    (ObliviousBuilderSemantics.emit_value selected.2 input (.and trial.valid condition)
      (inputShape.trans beforeAnd.inputs.symm))
  change Extension network valid.2 ∧ trial.state = trial.state ∧
    read valid.2 input valid.1 =
      (read network input trial.valid && read network input condition) ∧
    WordHolds input (fun bit : Fin 5 => if read network input trial.valid then
      reason.testBit bit.val else read network input trial.failure[bit]) valid.2 selected.1
  refine ⟨beforeAnd.trans andExtension, rfl, ?_, ?_⟩
  · change read valid.2 input valid.1 =
      (read selected.2 input trial.valid && read selected.2 input condition) at andValue
    rw [beforeAnd.read input trial.valid inputShape validBound,
      beforeAnd.read input condition inputShape conditionBound] at andValue
    exact andValue
  · apply WordHolds.extends andExtension
    refine ⟨inputShape.trans beforeAnd.inputs.symm, ?_⟩
    intro bit
    refine ⟨(selectedFacts.2 bit).1, ?_⟩
    have value := (selectedFacts.2 bit).2
    rw [errorFacts.1.read input trial.valid inputShape validBound,
      (errorFacts.2.2 bit).2,
      errorFacts.1.read input trial.failure[bit] inputShape (failureBound bit)] at value
    exact value

#assert_axioms finish_selects
#assert_axioms guard_selects
end Minidregg.Compiler.BendObliviousRollbackSemantics
