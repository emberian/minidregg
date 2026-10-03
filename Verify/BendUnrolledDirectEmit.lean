import Assurance.BendObliviousMinimal
import Compiler.ObliviousUnrollSemantics
import Host.BendProofWitness
import Compiler.BendTraceDirect

/- Actual admitted Lab yes → full controller → two raw ticks → shared DAG →
emitted arithmetic descriptor. All fixture data are public. This is a native
backend qualification consumer, not private world proof admission. -/
namespace Minidregg.Verify.BendUnrolledDirectEmit
open Compiler Theory
open ObliviousNetwork ObliviousUnroll BendClosureMachine
open Assurance.BendObliviousMinimal

def degree : BendTraceIR2.RowExpr BabyBear → Nat
  | .constant _ => 0
  | .loc _ => 1
  | .add a b => max (degree a) (degree b)
  | .mul a b => degree a + degree b

def inBounds (width : Nat) : BendTraceIR2.RowExpr BabyBear → Bool
  | .constant _ => true
  | .loc column => column < width
  | .add a b | .mul a b => inBounds width a && inBounds width b

def residue (row : Array Nat) : BendTraceIR2.RowExpr BabyBear → Nat
  | .constant value => value.val
  | .loc column => row[column]?.getD 0
  | .add a b => (residue row a + residue row b) % 2013265921
  | .mul a b => (residue row a * residue row b) % 2013265921

def emitFixture (directory : System.FilePath) : IO Unit := do
  let some input := prepare | throw (IO.userError "minimal source admission/prepare refused")
  let layout := build input.prepared.network ticks
  let network := layout.network
  if !network.valid then throw (IO.userError "generated unrolled graph invalid")
  let values := network.evaluateWires input.bits
  let output := network.outputs.map (fun index => values[index]?.getD false)
  if output[0]? != some true then throw (IO.userError "unrolled handled bit refused")
  let resultBits := output.extract 1 output.size
  let some state := BendObliviousCodec.decode shape resultBits |
    throw (IO.userError "unrolled final state failed decoding")
  let .complete pointer := state.control | throw (IO.userError "unrolled state did not complete")
  let some result := BendClosureArena.decode input.prepared.compiled.library.program state.heap 8 pointer |
    throw (IO.userError "completed value failed decoding")
  if result.term != source || state.sourceSteps != 0 then
    throw (IO.userError "actual source result differs from independently expected Lab yes/count0")
  let pins := (List.range network.inputCount) ++ network.outputs.toList
  let plan := BendTraceDirect.lower
    (BendTraceConstraints.constraints (F := BabyBear) network)
    (network.inputCount + network.gates.size) pins
  let witness := values.map (fun value => if value then 1 else 0)
  -- Public constructor check: no unnoticed higher-degree arithmetic enters this profile.
  for constraint in plan.constraints do
    match constraint with
    | .zero expression =>
      if degree expression > 2 || !inBounds witness.size expression then
        throw (IO.userError "direct AIR exceeds quadratic local-row profile")
      if residue witness expression != 0 then
        throw (IO.userError "actual Boolean network witness violates direct AIR")
    | .pi column _ =>
      if column >= witness.size then throw (IO.userError "public pin out of bounds")
  let publicValues := pins.toArray.map (fun index => witness[index]?.getD 0)
  let wrongInput := publicValues.setIfInBounds 0 (1 - (publicValues[0]?.getD 0))
  let wrongHandled := publicValues.setIfInBounds network.inputCount 0
  let last := publicValues.size - 1
  let wrongOutput := publicValues.setIfInBounds last (1 - (publicValues[last]?.getD 0))
  IO.FS.createDirAll directory
  IO.FS.writeFile (directory / "descriptor.json") (plan.toWire ++ "\n")
  IO.FS.writeFile (directory / "trace.csv") (BendProofWitness.csv witness)
  IO.FS.writeFile (directory / "public.csv") (BendProofWitness.csv publicValues)
  IO.FS.writeFile (directory / "wrong-input.csv") (BendProofWitness.csv wrongInput)
  IO.FS.writeFile (directory / "wrong-handled.csv") (BendProofWitness.csv wrongHandled)
  IO.FS.writeFile (directory / "wrong-output.csv") (BendProofWitness.csv wrongOutput)
  IO.println s!"ACTUAL source-admitted full controller: ticks={ticks} inputs={network.inputCount} gates={network.gates.size} arithmeticWires={plan.width} publicPins={publicValues.size}; decoded Lab yes/count0"

end Minidregg.Verify.BendUnrolledDirectEmit

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: BendUnrolledDirectEmit fixture-directory")
  Minidregg.Verify.BendUnrolledDirectEmit.emitFixture directory
