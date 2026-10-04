/- Actual Objective source through the generated code/thunk graph. The
reference source machine is used only to check the result, never to produce
the circuit output. This covers the declared initial dispatch tranche. -/
import Compiler.ObjectiveDemandPhysical
import Theory.AssertCompiled

namespace Minidregg.Assurance.ObjectiveDemandPhysicalChecks
open Minidregg.Compiler
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
set_option autoImplicit false

def shape : ObjectiveThunkNetwork.Shape := ⟨4,11,2,2⟩
def layout : ObjectiveDemandLayout.Layout :=
  { shape, codeSlots := 8, codeFieldSlots := 4, nameSlots := 2, nameBytes := 15,
    environmentSlots := 2, environmentWidth := 2, recordSlots := 2, recordWidth := 2,
    depth := 64 }

/-- The graph's two-tick result, read by the layout decoder, is EQUAL (by a
proof-producing comparison) to the source machine's two-step state. -/
def agrees (source : Term) : Bool :=
  match ObjectiveDemandPhysical.prepare ⟨128,32,128⟩ layout source with
  | none => false
  | some prepared =>
    match ObjectiveDemandPhysical.runGraph prepared.graph 2 prepared.initialBits with
    | none => false
    | some final =>
      match ObjectiveDemandPhysical.result layout final with
      | none => false
      | some (actual,suspended) =>
        !suspended && (ObjectiveDemandStateEquality.state layout.depth actual
          (run ⟨shape.heapSlots,shape.stackSlots⟩ 2 (initial source))).isSome

theorem natural_uses_source_rom_and_graph : agrees (.nat 7) = true := by native_decide
theorem boolean_uses_source_rom_and_graph : agrees (.boolean true) = true := by native_decide
theorem label_uses_source_rom_and_graph : agrees (.label "private-label") = true := by native_decide
theorem closure_uses_source_rom_and_graph : agrees (.lam (.bound 0)) = true := by native_decide

def tooWideRefuses : Bool :=
  match ObjectiveDemandPhysical.prepare ⟨128,32,128⟩ layout (.nat 16) with
  | none => true | some _ => false
theorem source_natural_overflow_refuses_before_graph : tooWideRefuses = true := by native_decide

def unsupportedRefuses : Bool :=
  match ObjectiveDemandPhysical.prepare ⟨128,32,128⟩ layout (.app (.lam (.bound 0)) (.nat 3)) with
  | none => false
  | some prepared =>
    match ObjectiveDemandPhysical.runGraph prepared.graph 1 prepared.initialBits with
    | none => true | some _ => false
theorem unsupported_application_is_not_success : unsupportedRefuses = true := by native_decide

#assert_compiled natural_uses_source_rom_and_graph
#assert_compiled boolean_uses_source_rom_and_graph
#assert_compiled label_uses_source_rom_and_graph
#assert_compiled closure_uses_source_rom_and_graph
#assert_compiled source_natural_overflow_refuses_before_graph
#assert_compiled unsupported_application_is_not_success
end Minidregg.Assurance.ObjectiveDemandPhysicalChecks

