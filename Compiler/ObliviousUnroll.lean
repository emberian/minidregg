import Compiler.BendTraceEvaluation

/- Public fixed-capacity composition of the SAME gate network. Raw state wires
are carried between blocks; every handled bit is conjoined inside the graph.
This is an actual DAG producer, not a host iteration offered as a proof. -/
namespace Minidregg.Compiler.ObliviousUnroll
open ObliviousNetwork BendTraceConstraints BendTraceEvaluation
set_option autoImplicit false

def mapOp (rename : Nat → Nat) : Op → Op
  | .constant value => .constant value
  | .xor a b => .xor (rename a) (rename b)
  | .and a b => .and (rename a) (rename b)

theorem mapOp_value (rename : Nat → Nat) (wires : Nat → Bool) (op : Op) :
    opValue wires (mapOp rename op) = opValue (fun i => wires (rename i)) op := by
  cases op <;> rfl

structure Placement where
  inputWires : Array Nat
  /-- Absolute wire address of the first gate in this copy. -/
  gateBase : Nat
  deriving DecidableEq, Repr

def Placement.wire (placement : Placement) (inputCount index : Nat) : Nat :=
  if index < inputCount then placement.inputWires[index]?.getD 0
  else placement.gateBase + (index - inputCount)

/-- Structural certificate: each original gate occurs literally at its mapped
SSA position. This can be checked without knowing any private input bit. -/
def Placement.Embedded (placement : Placement) (original whole : Network) : Prop :=
  whole.inputCount ≤ placement.gateBase ∧
  ∀ row ∈ original.gates.toList.zipIdx,
    (mapOp (placement.wire original.inputCount) row.1,
      placement.gateBase - whole.inputCount + row.2) ∈ whole.gates.toList.zipIdx

def Placement.check (placement : Placement) (original whole : Network) : Bool :=
  decide (whole.inputCount ≤ placement.gateBase) &&
  original.gates.toList.zipIdx.all (fun row =>
    decide ((mapOp (placement.wire original.inputCount) row.1,
      placement.gateBase - whole.inputCount + row.2) ∈ whole.gates.toList.zipIdx))

theorem placement_check (placement : Placement) (original whole : Network) :
    placement.check original whole = true ↔ placement.Embedded original whole := by
  simp [Placement.check, Placement.Embedded, Bool.and_eq_true, List.all_eq_true]

/-- Any satisfying whole-graph assignment restricts to the original block's
actual gate equations. Gate intermediates cannot be chosen independently. -/
theorem embedded_graph (placement : Placement) (original whole : Network)
    (embedded : placement.Embedded original whole)
    (wires : Nat → Bool) (graph : BooleanGraph whole wires) :
    BooleanGraph original (fun index => wires (placement.wire original.inputCount index)) := by
  intro row member
  have equation := graph _ (embedded.2 row member)
  have baseBound := embedded.1
  have address : whole.inputCount +
      (placement.gateBase - whole.inputCount + row.2) = placement.gateBase + row.2 := by
    omega
  have notInput : ¬ original.inputCount + row.2 < original.inputCount := by omega
  simpa only [address, mapOp_value, Placement.wire, notInput,
    if_false, Nat.add_sub_cancel_left] using equation

theorem embedded_evaluate (placement : Placement) (original whole : Network)
    (embedded : placement.Embedded original whole) (valid : original.valid = true)
    (input : Array Bool) (shape : input.size = original.inputCount)
    (wires : Nat → Bool) (graph : BooleanGraph whole wires)
    (pinned : ∀ i < original.inputCount,
      input[i]?.getD false = wires (placement.wire original.inputCount i)) :
    original.evaluate input = some (original.outputs.map
      (fun index => wires (placement.wire original.inputCount index))) :=
  evaluate_forced original input valid shape _
    (embedded_graph placement original whole embedded wires graph) pinned

structure Layout where
  network : Network
  stateWires : Array Nat
  handledWire : Nat
  copies : Array Placement
  deriving DecidableEq, Repr

/-- One literal gate-copy followed by a counted AND of its handled bit with
all earlier handled bits. State outputs retain their raw wire representation. -/
def append (original : Network) (layout : Layout) : Layout :=
  let placement : Placement :=
    ⟨layout.stateWires, layout.network.inputCount + layout.network.gates.size⟩
  let rename := placement.wire original.inputCount
  let copied := original.gates.map (mapOp rename)
  let handled := rename (original.outputs[0]?.getD 0)
  let nextHandled := layout.network.inputCount + layout.network.gates.size + copied.size
  { network := { layout.network with
      gates := (layout.network.gates ++ copied).push (.and layout.handledWire handled) }
    stateWires := (original.outputs.extract 1 original.outputs.size).map rename
    handledWire := nextHandled
    copies := layout.copies.push placement }

def iterate (original : Network) : Nat → Layout → Layout
  | 0, layout => layout
  | ticks + 1, layout => iterate original ticks (append original layout)

def build (original : Network) (ticks : Nat) : Layout :=
  let initial : Layout :=
    { network := { inputCount := original.inputCount, gates := #[.constant true] }
      stateWires := Array.range original.inputCount
      handledWire := original.inputCount
      copies := #[] }
  let result := iterate original ticks initial
  { result with network := { result.network with
      outputs := #[result.handledWire] ++ result.stateWires } }

/-- Fail closed on the original state width and actual final SSA validity.
The source/controller correspondence is a separate theorem obligation. -/
def checked (original : Network) (ticks : Nat) : Option Layout :=
  if original.valid && original.outputs.size == original.inputCount + 1 then
    let result := build original ticks
    if result.network.valid then some result else none
  else none

#assert_axioms mapOp_value
#assert_axioms placement_check
#assert_axioms embedded_graph
#assert_axioms embedded_evaluate
end Minidregg.Compiler.ObliviousUnroll
