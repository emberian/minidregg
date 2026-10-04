/- Concrete Objective source-to-initial-physical-state producer. The actual
compiler, bounded table packer and the layout's one decoder (state region plus
every table region, ObjectiveDemandRegions) establish the initial source
interpretation. The current generated controller covers an explicit
opcode tranche; construction of a program does not assert all-run coverage. -/
import Compiler.ObjectiveDemandRegions
import Compiler.ObjectiveDemandLiteralNetwork
import Compiler.ObjectiveDemandStateEquality

namespace Minidregg.Compiler.ObjectiveDemandPhysical
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open ObjectiveDemandCode ObjectiveDemandStorage ObjectiveDemandLayout
set_option autoImplicit false

/-- A program prepared for the graph of a public layout. `initialExact` is the
initial-state premise of the receivers, discharged by translation validation:
the layout's one decoder, applied to the complete initial bits (state region and
every table region), returns the source machine's initial state. -/
structure Prepared (source : Minidregg.Theory.ObjectiveBendOpenRecursion.Term) (layout : Layout) where
  compiled : Compiled source
  packed : ObjectiveDemandPackedCode.Encoded compiled.program layout.word layout.codeFieldSlots
  graph : ObliviousNetwork.Network
  initialBits : Array Bool
  graphExact : ObjectiveDemandLiteralNetwork.network layout = some graph
  initialShape : initialBits.size = graph.inputCount
  initialExact : ObjectiveDemandRegions.state layout initialBits = some (initial source)

def ofCompiled {source : Minidregg.Theory.ObjectiveBendOpenRecursion.Term}
    (compiled : Compiled source) (layout : Layout) : Option (Prepared source layout) := do
  let packed ← ObjectiveDemandPackedCode.encode compiled.program layout.word layout.codeFieldSlots
  match selected : ObjectiveDemandLiteralNetwork.network layout with
  | none => none
  | some graph =>
    let initialBits ← ObjectiveDemandRegions.encode layout (initialRef compiled.entry) packed.table
      (initialTables compiled.program).environments (initialTables compiled.program).fields
    if shaped : initialBits.size = graph.inputCount then
      match decoded : ObjectiveDemandRegions.state layout initialBits with
      | none => none
      | some state =>
        match ObjectiveDemandStateEquality.state layout.depth state (initial source) with
        | none => none
        | some same =>
          pure ⟨compiled, packed, graph, initialBits, selected, shaped,
            by rw [decoded, same.down]⟩
    else none

def prepare (limits : ObjectiveDemandCode.Limits) (layout : Layout)
    (source : Minidregg.Theory.ObjectiveBendOpenRecursion.Term) : Option (Prepared source layout) := do
  ofCompiled (← ObjectiveDemandCode.compile limits source) layout

/-- Raw graph output state is carried unchanged between physical ticks.
Handled=false is an explicit unsupported/invalid physical transition, not a
successful source result. This is clear conformance evaluation, not MPC. -/
def runGraph (graph : ObliviousNetwork.Network) : Nat → Array Bool → Option (Array Bool)
  | 0,input => some input
  | ticks+1,input => do
    let output ← graph.evaluate input
    if output[0]?.getD false then runGraph graph ticks (output.extract 1 output.size) else none

/-- The physical result: the layout's one decoder. No program enters it. -/
def result (layout : Layout) (input : Array Bool) : Option (State × Bool) :=
  ObjectiveDemandRegions.decode layout input

/-- At the same public layout, the generated gates are independent of source
contents. Program bits remain inputs; this alone is not an MPC/privacy proof,
but it prevents source-dependent constant-ROM specialization here. -/
theorem graph_source_independent
    {leftSource rightSource : Minidregg.Theory.ObjectiveBendOpenRecursion.Term}
    {layout : Layout} (left : Prepared leftSource layout) (right : Prepared rightSource layout) :
    left.graph = right.graph :=
  Option.some.inj (left.graphExact.symm.trans right.graphExact)

#assert_axioms graph_source_independent

end Minidregg.Compiler.ObjectiveDemandPhysical

