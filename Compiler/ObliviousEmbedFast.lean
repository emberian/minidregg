import Compiler.ObliviousUnroll

namespace Minidregg.Compiler.ObliviousUnroll
open ObliviousNetwork
set_option autoImplicit false

/-- Linear structural check: compare each copied gate at its exact SSA index,
rather than repeatedly searching the whole gate list. -/
def Placement.fastCheck (placement : Placement) (original whole : Network) : Bool :=
  decide (whole.inputCount ≤ placement.gateBase) &&
  original.gates.toList.zipIdx.all (fun row =>
    whole.gates[placement.gateBase - whole.inputCount + row.2]? ==
      some (mapOp (placement.wire original.inputCount) row.1))

theorem placement_fastCheck (placement : Placement) (original whole : Network) :
    placement.fastCheck original whole = true ↔ placement.Embedded original whole := by
  simp [Placement.fastCheck, Placement.Embedded, Bool.and_eq_true,
    List.all_eq_true, List.mk_mem_zipIdx_iff_getElem?]

#assert_axioms placement_fastCheck
end Minidregg.Compiler.ObliviousUnroll
