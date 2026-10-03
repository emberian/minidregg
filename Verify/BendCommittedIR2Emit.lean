import Compiler.BendCommittedNetworkChecks
import Host.BendProofWitness

/- Joined proof fixture: compute one private XOR byte, canonically frame that
SAME output with public Context and private salt, and hash inside one graph.
The sample Context is not an authority token or an admitted world invocation. -/
namespace Minidregg.Verify.BendCommittedIR2Emit
open Compiler BendCommittedNetworkChecks

def emitFixture (privatePath directory : System.FilePath) : IO Unit := do
  let bytes := (← IO.FS.readBinFile privatePath).toList
  if bytes.length != 34 then throw (IO.userError "expected two private inputs plus 32 salt bytes")
  let left := bytes[0]?.getD 0
  let right := bytes[1]?.getD 0
  let coins := bytes.drop 2
  let some prepared := BendCommittedNetwork.prepare execution domain context 1 execution.outputs |
    throw (IO.userError "actual shared-wire graph preparation refused")
  let graph := prepared.candidate.whole
  let inputs := BendProofCshake.bits [left, right] ++ BendProofCshake.bits coins ++ #[false, true]
  let values := graph.evaluateWires inputs
  let output := graph.outputs.map (fun index => values[index]?.getD false)
  let expected := BendProofCshake.bits [left ^^^ right] ++ #[true] ++
    BendProofCshake.bits (Sp800185Cshake256.cshake256Bytes domain.toUTF8.toList
      (BendCommitmentFrame.frameBytes context coins [left ^^^ right]))
  if output != expected then throw (IO.userError "shared execution/frame/hash differs from independent source bytes")
  -- Only the commitment validity and digest are public; XOR output stays private.
  let pins := graph.outputs.extract 8 graph.outputs.size
  let plan := BendTraceDirect.lower
    (BendTraceConstraints.constraints (F := BabyBear) graph)
    (graph.inputCount + graph.gates.size) pins.toList
  let witness := values.map (fun value => if value then 1 else 0)
  let publicValues := (expected.extract 8 expected.size).map (fun value => if value then 1 else 0)
  IO.FS.createDirAll directory
  IO.FS.writeFile (directory / "descriptor.json") (plan.toWire ++ "\n")
  IO.FS.writeFile (directory / "trace.csv") (Host.BendProofWitness.csv witness)
  IO.FS.writeFile (directory / "public.csv") (Host.BendProofWitness.csv publicValues)
  IO.FS.writeFile (directory / "wrong-digest.csv")
    (Host.BendProofWitness.csv (publicValues.setIfInBounds 1 (1 - (publicValues[1]?.getD 0))))
  IO.FS.writeFile (directory / "wrong-validity.csv")
    (Host.BendProofWitness.csv (publicValues.setIfInBounds 0 0))
  IO.println s!"ACTUAL shared execution/canonical-frame/hash: gates={graph.gates.size} arithmeticWires={plan.width} publicPins={publicValues.size}; no private values printed"
end Minidregg.Verify.BendCommittedIR2Emit

def main (args : List String) : IO Unit := do
  let [privatePath, directory] := args |
    throw (IO.userError "usage: BendCommittedIR2Emit private-input-file fixture-directory")
  Minidregg.Verify.BendCommittedIR2Emit.emitFixture privatePath directory
