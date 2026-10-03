import Assurance.BendObliviousMinimal
import Compiler.BendCommittedRun
import Compiler.BendCommittedNetworkChecks
import Host.BendProofWitness

/- Actual admitted controller and salted commitment in ONE graph. The payload
is the explicit v1 padded RAW final-state codec, not a world Result codec.
Public initial state, combined execution/hash validity, and digest are pinned.
The diagnostic Context does not grant world authorization. -/
namespace Minidregg.Verify.BendControllerCommitmentEmit
open Compiler Theory
open Assurance.BendObliviousMinimal

/-- Little-endian byte packing with zero padding in the final byte. -/
def rawBytes (bits : Array Bool) : List UInt8 :=
  (List.range ((bits.size + 7) / 8)).map fun byte =>
    UInt8.ofNat ((List.range 8).foldl (fun total bit =>
      total + if bits[byte * 8 + bit]?.getD false then 2 ^ bit else 0) 0)

def domain : String := "DREGG.BEND.RAW-STATE-DIAGNOSTIC/v1"

def emitFixture (saltPath directory : System.FilePath) : IO Unit := do
  let coins := (← IO.FS.readBinFile saltPath).toList
  if coins.length != 32 then throw (IO.userError "expected 32 private salt bytes")
  let some admitted := prepare | throw (IO.userError "actual source admission refused")
  let unrolled := (ObliviousUnroll.build admitted.prepared.network ticks).network
  let values := unrolled.evaluateWires admitted.bits
  let output := unrolled.outputs.map (fun wire => values[wire]?.getD false)
  if output[0]? != some true then throw (IO.userError "actual source controller refused")
  let finalBits := output.extract 1 output.size
  let some final := BendObliviousCodec.decode shape finalBits |
    throw (IO.userError "actual raw state decode refused")
  let .complete pointer := final.control | throw (IO.userError "actual controller incomplete")
  let some decoded := BendClosureArena.decode admitted.prepared.compiled.library.program final.heap 8 pointer |
    throw (IO.userError "actual result decode refused")
  if decoded.term != source || final.sourceSteps != 0 then
    throw (IO.userError "actual admitted source result mismatch")
  let payload := rawBytes finalBits
  let capacity := payload.length
  let padding := unrolled.inputCount + unrolled.gates.size
  let execution := { unrolled with gates := unrolled.gates.push (.constant false) }
  let payloadWires := (unrolled.outputs.extract 1 unrolled.outputs.size) ++
    Array.replicate (capacity * 8 - finalBits.size) padding
  let context := BendCommittedNetworkChecks.context
  let some prepared := BendCommittedNetwork.prepare execution domain context capacity payloadWires |
    throw (IO.userError "actual shared controller/frame preparation refused")
  let some graph := BendCommittedRun.fromCandidate execution prepared.candidate |
    throw (IO.userError "combined execution/commitment success gate refused")
  let inputs := admitted.bits ++ BendProofCshake.bits coins ++
    (Array.range (capacity + 1)).map (· == capacity)
  let wires := graph.evaluateWires inputs
  let actual := graph.outputs.map (fun wire => wires[wire]?.getD false)
  let digest := BendProofCshake.bits (Sp800185Cshake256.cshake256Bytes domain.toUTF8.toList
    (BendCommitmentFrame.frameBytes context coins payload))
  if actual != #[true] ++ output ++ #[true] ++ digest then
    throw (IO.userError "controller shared raw payload/frame/hash mismatch")
  let pins := #[graph.outputs[0]?.getD 0] ++ Array.range unrolled.inputCount ++
    graph.outputs.extract (execution.outputs.size + 2) graph.outputs.size
  let plan := BendTraceDirect.lower (BendTraceConstraints.constraints (F := BabyBear) graph)
    (graph.inputCount + graph.gates.size) pins.toList
  let witness := wires.map (fun value => if value then 1 else 0)
  let publicValues := pins.map (fun index => witness[index]?.getD 0)
  IO.FS.createDirAll directory
  IO.FS.writeFile (directory / "descriptor.json") (plan.toWire ++ "\n")
  IO.FS.writeFile (directory / "trace.csv") (Host.BendProofWitness.csv witness)
  IO.FS.writeFile (directory / "public.csv") (Host.BendProofWitness.csv publicValues)
  IO.FS.writeFile (directory / "wrong-digest.csv") (Host.BendProofWitness.csv
    (publicValues.setIfInBounds (1 + unrolled.inputCount)
      (1 - (publicValues[1 + unrolled.inputCount]?.getD 0))))
  IO.FS.writeFile (directory / "wrong-validity.csv")
    (Host.BendProofWitness.csv (publicValues.setIfInBounds 0 0))
  IO.FS.writeFile (directory / "wrong-input.csv")
    (Host.BendProofWitness.csv (publicValues.setIfInBounds 1 (1 - (publicValues[1]?.getD 0))))
  IO.println s!"ACTUAL source controller+private salt+shared raw state commitment: ticks={ticks} gates={graph.gates.size} arithmeticWires={plan.width} publicPins={publicValues.size}; no private salt printed"
end Minidregg.Verify.BendControllerCommitmentEmit

def main (args : List String) : IO Unit := do
  let [saltPath, directory] := args |
    throw (IO.userError "usage: BendControllerCommitmentEmit private-salt-file fixture-directory")
  Minidregg.Verify.BendControllerCommitmentEmit.emitFixture saltPath directory
