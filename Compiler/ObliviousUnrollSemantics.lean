import Compiler.ObliviousUnroll

namespace Minidregg.Compiler.ObliviousUnroll
open ObliviousNetwork BendTraceConstraints
set_option autoImplicit false

theorem graph_prefix (original : Network) (suffix : Array Op)
    (wires : Nat → Bool)
    (graph : BooleanGraph { original with gates := original.gates ++ suffix } wires) :
    BooleanGraph original wires := by
  intro row member
  apply graph row
  apply List.mk_mem_zipIdx_iff_getElem?.mpr
  have indexed := List.mk_mem_zipIdx_iff_getElem?.mp member
  have bounded : row.2 < original.gates.size := by
    simpa using (List.getElem?_eq_some_iff.mp indexed).1
  simpa [Array.toList_append, List.getElem?_append, bounded] using indexed

theorem append_graph_prefix (original : Network) (layout : Layout)
    (wires : Nat → Bool) (graph : BooleanGraph (append original layout).network wires) :
    BooleanGraph layout.network wires := by
  apply graph_prefix layout.network
    ((original.gates.map (mapOp (Placement.wire
      ⟨layout.stateWires, layout.network.inputCount + layout.network.gates.size⟩
      original.inputCount))).push
      (.and layout.handledWire
        (Placement.wire ⟨layout.stateWires, layout.network.inputCount + layout.network.gates.size⟩
          original.inputCount (original.outputs[0]?.getD 0)))) wires
  simpa only [append, Array.append_push] using graph

theorem append_embedded (original : Network) (layout : Layout) :
    (Placement.mk layout.stateWires
      (layout.network.inputCount + layout.network.gates.size)).Embedded original
      (append original layout).network := by
  constructor
  · simp [append]
  · intro row member
    apply List.mk_mem_zipIdx_iff_getElem?.mpr
    have indexed := List.mk_mem_zipIdx_iff_getElem?.mp member
    have bounded : row.2 < original.gates.size := by
      simpa using (List.getElem?_eq_some_iff.mp indexed).1
    simp only [append, Array.toList_push, Array.toList_append, Array.toList_map,
      Nat.add_sub_cancel_left]
    rw [List.getElem?_append_left (by simp; omega)]
    rw [List.getElem?_append_right (by simp)]
    simp only [Array.length_toList, Nat.add_sub_cancel_left]
    simpa using congrArg (Option.map (mapOp
      (Placement.wire ⟨layout.stateWires, layout.network.inputCount + layout.network.gates.size⟩
        original.inputCount))) indexed

/-- The appended AND really constrains the cumulative handled bit. -/
theorem append_handled (original : Network) (layout : Layout)
    (wires : Nat → Bool) (graph : BooleanGraph (append original layout).network wires) :
    wires (append original layout).handledWire =
      (wires layout.handledWire && wires
        (Placement.wire ⟨layout.stateWires, layout.network.inputCount + layout.network.gates.size⟩
          original.inputCount (original.outputs[0]?.getD 0))) := by
  let placement : Placement := ⟨layout.stateWires, layout.network.inputCount + layout.network.gates.size⟩
  let copied := original.gates.map (mapOp (placement.wire original.inputCount))
  have member : (.and layout.handledWire
      (placement.wire original.inputCount (original.outputs[0]?.getD 0)),
      layout.network.gates.size + copied.size) ∈
      (append original layout).network.gates.toList.zipIdx := by
    apply List.mk_mem_zipIdx_iff_getElem?.mpr
    simp [append, placement, copied]
  simpa only [append, opValue, Array.size_map, placement, copied, Nat.add_assoc]
    using graph _ member

def stateValues (wires : Nat → Bool) (layout : Layout) : Array Bool :=
  layout.stateWires.map wires

theorem append_evaluate (original : Network) (layout : Layout)
    (valid : original.valid = true)
    (shape : layout.stateWires.size = original.inputCount)
    (wires : Nat → Bool) (graph : BooleanGraph (append original layout).network wires) :
    original.evaluate (stateValues wires layout) =
      some (original.outputs.map (fun index => wires
        (Placement.wire ⟨layout.stateWires, layout.network.inputCount + layout.network.gates.size⟩
          original.inputCount index))) := by
  apply embedded_evaluate _ original (append original layout).network
    (append_embedded original layout) valid _ (by simp [stateValues, shape]) wires graph
  intro i bounded
  have indexBound : i < layout.stateWires.size := by omega
  simp [stateValues, Placement.wire, bounded, Array.getElem?_eq_getElem indexBound]

theorem iterate_graph_prefix (original : Network) (ticks : Nat) (layout : Layout)
    (wires : Nat → Bool) (graph : BooleanGraph (iterate original ticks layout).network wires) :
    BooleanGraph layout.network wires := by
  induction ticks generalizing layout with
  | zero => exact graph
  | succ ticks ih => exact append_graph_prefix original layout wires (ih _ graph)

theorem iterate_handled (original : Network) (ticks : Nat) (layout : Layout)
    (wires : Nat → Bool) (graph : BooleanGraph (iterate original ticks layout).network wires)
    (accepted : wires (iterate original ticks layout).handledWire = true) :
    wires layout.handledWire = true := by
  induction ticks generalizing layout with
  | zero => exact accepted
  | succ ticks ih =>
    have next := ih (append original layout) graph accepted
    have prefixGraph := iterate_graph_prefix original ticks (append original layout) wires graph
    rw [append_handled original layout wires prefixGraph] at next
    simp only [Bool.and_eq_true] at next
    exact next.1

/-- Successful raw execution, without host decoding or reencoding of state. -/
inductive AcceptedRun (original : Network) : Nat → Array Bool → Array Bool → Prop
  | done (input : Array Bool) : AcceptedRun original 0 input input
  | step {ticks : Nat} {input intermediate result : Array Bool}
      (evaluated : original.evaluate input = some intermediate)
      (handled : intermediate[0]? = some true)
      (tail : AcceptedRun original ticks (intermediate.extract 1 intermediate.size) result) :
      AcceptedRun original (ticks + 1) input result

theorem append_success (original : Network) (layout : Layout)
    (valid : original.valid = true) (width : original.outputs.size = original.inputCount + 1)
    (shape : layout.stateWires.size = original.inputCount)
    (wires : Nat → Bool) (graph : BooleanGraph (append original layout).network wires)
    (accepted : wires (append original layout).handledWire = true) :
    ∃ output, original.evaluate (stateValues wires layout) = some output ∧
      output[0]? = some true ∧
      output.extract 1 output.size = stateValues wires (append original layout) := by
  let rename := Placement.wire
    ⟨layout.stateWires, layout.network.inputCount + layout.network.gates.size⟩ original.inputCount
  refine ⟨original.outputs.map (fun index => wires (rename index)),
    append_evaluate original layout valid shape wires graph, ?_, ?_⟩
  · have both := (append_handled original layout wires graph).symm.trans accepted
    simp only [Bool.and_eq_true] at both
    have handled := both.2
    have nonempty : 0 < original.outputs.size := by omega
    simpa [rename, Array.getElem?_eq_getElem nonempty] using handled
  · simp [stateValues, append, rename, Array.map_map, Function.comp_def]

theorem iterate_success (original : Network) (ticks : Nat) (layout : Layout)
    (valid : original.valid = true) (width : original.outputs.size = original.inputCount + 1)
    (shape : layout.stateWires.size = original.inputCount)
    (wires : Nat → Bool) (graph : BooleanGraph (iterate original ticks layout).network wires)
    (accepted : wires (iterate original ticks layout).handledWire = true) :
    AcceptedRun original ticks (stateValues wires layout)
      (stateValues wires (iterate original ticks layout)) := by
  induction ticks generalizing layout with
  | zero => exact .done _
  | succ ticks ih =>
    have prefixGraph := iterate_graph_prefix original ticks (append original layout) wires graph
    have nextHandled := iterate_handled original ticks (append original layout) wires graph accepted
    obtain ⟨output, evaluated, handled, stateExact⟩ :=
      append_success original layout valid width shape wires prefixGraph nextHandled
    apply AcceptedRun.step evaluated handled
    rw [stateExact]
    apply ih _ ?_ graph accepted
    simp [append, width]

theorem iterate_inputCount (original : Network) (ticks : Nat) (layout : Layout) :
    (iterate original ticks layout).network.inputCount = layout.network.inputCount := by
  induction ticks generalizing layout with
  | zero => rfl
  | succ ticks ih => exact ih (append original layout)

theorem build_inputCount (original : Network) (ticks : Nat) :
    (build original ticks).network.inputCount = original.inputCount :=
  iterate_inputCount original ticks _

theorem build_success (original : Network) (ticks : Nat)
    (valid : original.valid = true) (width : original.outputs.size = original.inputCount + 1)
    (wires : Nat → Bool) (graph : BooleanGraph (build original ticks).network wires)
    (accepted : wires (build original ticks).handledWire = true) :
    AcceptedRun original ticks ((Array.range original.inputCount).map wires)
      (stateValues wires (build original ticks)) := by
  let initial : Layout :=
    { network := { inputCount := original.inputCount, gates := #[.constant true] }
      stateWires := Array.range original.inputCount
      handledWire := original.inputCount
      copies := #[] }
  change AcceptedRun original ticks (stateValues wires initial)
    (stateValues wires (iterate original ticks initial))
  exact iterate_success original ticks initial valid width (by simp [initial]) wires graph accepted

#assert_axioms iterate_inputCount
#assert_axioms build_inputCount
#assert_axioms build_success
#assert_axioms append_success
#assert_axioms iterate_success
#assert_axioms append_evaluate
#assert_axioms iterate_graph_prefix
#assert_axioms iterate_handled
#assert_axioms graph_prefix
#assert_axioms append_graph_prefix
#assert_axioms append_embedded
#assert_axioms append_handled
end Minidregg.Compiler.ObliviousUnroll
