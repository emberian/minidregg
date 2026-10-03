import Compiler.ObliviousCompositeSemantics

namespace Minidregg.Compiler.ObliviousConstantSemantics
open ObliviousNetwork ObliviousWords ObliviousBuilderSemantics ObliviousMuxSemantics
open ObliviousWordSemantics ObliviousVectorSemantics ObliviousCompositeSemantics
set_option autoImplicit false

theorem emit_extension (network : Network) (op : Op) :
    Extension network ((emit op).run network).2 := by
  rw [emit_run]
  refine ⟨rfl, by simp, ?_⟩
  intro input wire earlier
  exact push_preserves network input op wire earlier

theorem emit_bound (network : Network) (op : Op) :
    let result := (emit op).run network
    result.1 < result.2.inputCount + result.2.gates.size := by
  simp only [emit_run, Array.size_push]
  omega

theorem constant_produces (network : Network) (input : Array Bool)
    (shape : input.size = network.inputCount) (width value : Nat) :
    let result := (constant width value).run network
    Extension network result.2 ∧
    WordHolds input (fun bit => value.testBit bit.val) result.2 result.1 := by
  have facts := ofFnM_produces network input shape
    (fun bit : Fin width => emit (.constant (value.testBit bit.val)))
    (fun bit => value.testBit bit.val) (by
      intro bit current extension
      refine ⟨emit_extension current _, emit_bound current _, ?_⟩
      exact congrArg (fun v => v.getD false)
        (emit_value current input (.constant (value.testBit bit.val))
          (shape.trans extension.inputs.symm))) network (Extension.refl network)
  exact ⟨facts.1, shape.trans facts.1.inputs.symm, facts.2⟩

#assert_axioms emit_extension
#assert_axioms emit_bound
#assert_axioms constant_produces
end Minidregg.Compiler.ObliviousConstantSemantics
