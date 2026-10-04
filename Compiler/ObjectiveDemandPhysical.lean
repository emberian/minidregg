/- Concrete Objective source-to-initial-physical-state producer. The actual
compiler, bounded table packer and actual state codec establish the initial
source interpretation. The current generated controller covers an explicit
opcode tranche; construction of a program does not assert all-run coverage. -/
import Compiler.ObjectiveDemandStateCodec
import Compiler.ObjectiveDemandLiteralNetwork

namespace Minidregg.Compiler.ObjectiveDemandPhysical
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open ObjectiveDemandCode ObjectiveDemandStorage
set_option autoImplicit false

def paddedTable (table : ObjectiveDemandPackedCode.Table) (codeSlots : Nat) :
    ObjectiveDemandPackedCode.Table :=
  {table with rows := (table.rows ++ Array.replicate (codeSlots-table.rows.size) (ObjectiveDemandPackedCode.Row.mk 31 0 0 0 0))}

structure Prepared (source : Minidregg.Theory.ObjectiveBendOpenRecursion.Term)
    (shape : ObjectiveThunkNetwork.Shape) where
  compiled : Compiled source
  packed : ObjectiveDemandPackedCode.Encoded compiled.program shape.wordBits (2^shape.wordBits-1)
  codeSlots : Nat
  graph : ObliviousNetwork.Network
  initialStateBits : Array Bool
  initialBits : Array Bool
  graphExact : ObjectiveDemandLiteralNetwork.network shape codeSlots = some graph
  bitsExact : initialBits = initialStateBits ++ (paddedTable packed.table codeSlots).codeBits shape.wordBits
  initialShape : initialBits.size = graph.inputCount
  decodedInitial : ObjectiveDemandStateCodec.decode shape initialStateBits =
    some (initialRef compiled.entry,false)
  initialMeaning : ObjectiveDemandStateCodec.represents shape
    (initialTables compiled.program) compiled.decodeDepth initialStateBits (initial source)

def ofCompiled {source : Minidregg.Theory.ObjectiveBendOpenRecursion.Term}
    (compiled : Compiled source) (shape : ObjectiveThunkNetwork.Shape) (codeSlots : Nat) : Option (Prepared source shape) := do
  let packed ← ObjectiveDemandPackedCode.encode compiled.program shape.wordBits (2^shape.wordBits-1)
  if packed.table.rows.size > codeSlots then none else do
    match selected : ObjectiveDemandLiteralNetwork.network shape codeSlots with
    | none => none
    | some graph =>
      let initialStateBits ← ObjectiveDemandStateCodec.encode shape (initialRef compiled.entry)
      if decoded : ObjectiveDemandStateCodec.decode shape initialStateBits =
          some (initialRef compiled.entry,false) then
        let padded := paddedTable packed.table codeSlots
        let initialBits := initialStateBits ++ padded.codeBits shape.wordBits
        if shaped : initialBits.size = graph.inputCount then
          pure ⟨compiled,packed,codeSlots,graph,initialStateBits,initialBits,selected,rfl,shaped,decoded,
            ⟨initialRef compiled.entry,false,decoded,ObjectiveDemandStorage.initial_exact compiled⟩⟩
        else none
      else none

def prepare (limits : ObjectiveDemandCode.Limits)
    (shape : ObjectiveThunkNetwork.Shape) (codeSlots : Nat)
    (source : Minidregg.Theory.ObjectiveBendOpenRecursion.Term) : Option (Prepared source shape) := do
  ofCompiled (← ObjectiveDemandCode.compile limits source) shape codeSlots

/-- Raw graph output state is carried unchanged between physical ticks.
Handled=false is an explicit unsupported/invalid physical transition, not a
successful source result. This is clear conformance evaluation, not MPC. -/
def runGraph (graph : ObliviousNetwork.Network) : Nat → Array Bool → Option (Array Bool)
  | 0,input => some input
  | ticks+1,input => do
    let output ← graph.evaluate input
    if output[0]?.getD false then runGraph graph ticks (output.extract 1 output.size) else none

def result {source : Minidregg.Theory.ObjectiveBendOpenRecursion.Term}
    {shape : ObjectiveThunkNetwork.Shape} (prepared : Prepared source shape)
    (input : Array Bool) : Option (State × Bool) := do
  let (reference,suspended) ← ObjectiveDemandStateCodec.decode shape (input.extract 0 shape.inputCount)
  pure (← ObjectiveDemandStorage.decode (initialTables prepared.compiled.program)
    prepared.compiled.decodeDepth reference,suspended)

theorem initial_source {source : Minidregg.Theory.ObjectiveBendOpenRecursion.Term}
    {shape : ObjectiveThunkNetwork.Shape} (prepared : Prepared source shape) :
    ObjectiveDemandStateCodec.represents shape (initialTables prepared.compiled.program)
      prepared.compiled.decodeDepth prepared.initialStateBits (initial source) :=
  prepared.initialMeaning

#assert_axioms initial_source

/-- At the same public capacities, the generated gates are independent of
source contents. Program bits remain inputs; this alone is not an MPC/privacy
proof, but it prevents source-dependent constant-ROM specialization here. -/
theorem graph_source_independent
    {leftSource rightSource : Minidregg.Theory.ObjectiveBendOpenRecursion.Term}
    {shape : ObjectiveThunkNetwork.Shape}
    (left : Prepared leftSource shape) (right : Prepared rightSource shape)
    (sameCapacity : left.codeSlots = right.codeSlots) : left.graph = right.graph := by
  have leftGraph := left.graphExact
  rw [sameCapacity] at leftGraph
  exact Option.some.inj (leftGraph.symm.trans right.graphExact)

#assert_axioms graph_source_independent

end Minidregg.Compiler.ObjectiveDemandPhysical

