import Compiler.BendProofCshakeBounded
import Compiler.BendTraceDirect
import Host.BendProofWitness

/- Native proof consumer of the actual salted-hash primitive. The private file
contains the preimage; it is not copied into public inputs. This qualification
fixture does not claim the preimage is an authorized invocation encoding.
A world consumer must constrain the canonical Context/coins/payload framing. -/
namespace Minidregg.Host.BendCommitmentIR2Emit
open Compiler
open BendProofCshakeBounded

def capacity : Nat := 64

def emitFixture (privatePath directory : System.FilePath) : IO Unit := do
  let preimage := (← IO.FS.readBinFile privatePath).toList
  if preimage.length > capacity then throw (IO.userError "private preimage exceeds public capacity")
  let domain := "DREGG.BEND.INPUT-COMMIT/v1".toUTF8.toList
  let graph := networkPublicPrefix domain capacity
  if !graph.valid then throw (IO.userError "bounded commitment graph invalid")
  let values := graph.evaluateWires (input capacity preimage)
  let output := graph.outputs.map (fun index => values[index]?.getD false)
  let expected := #[true] ++ BendProofCshake.bits (Sp800185Cshake256.cshake256Bytes domain preimage)
  if output != expected then throw (IO.userError "actual commitment graph differs from independent cSHAKE")
  let plan := BendTraceDirect.lower
    (BendTraceConstraints.constraints (F := BabyBear) graph)
    (graph.inputCount + graph.gates.size) graph.outputs.toList
  let witness := values.map (fun value => if value then 1 else 0)
  let publicValues := expected.map (fun value => if value then 1 else 0)
  let wrongDigest := publicValues.setIfInBounds 1 (1 - (publicValues[1]?.getD 0))
  let wrongValidity := publicValues.setIfInBounds 0 0
  IO.FS.createDirAll directory
  IO.FS.writeFile (directory / "descriptor.json") (plan.toWire ++ "\n")
  IO.FS.writeFile (directory / "trace.csv") (BendProofWitness.csv witness)
  IO.FS.writeFile (directory / "public.csv") (BendProofWitness.csv publicValues)
  IO.FS.writeFile (directory / "wrong-digest.csv") (BendProofWitness.csv wrongDigest)
  IO.FS.writeFile (directory / "wrong-validity.csv") (BendProofWitness.csv wrongValidity)
  IO.println s!"ACTUAL bounded commitment: capacity={capacity} gates={graph.gates.size} arithmeticWires={plan.width} publicPins={publicValues.size}; preimage and length remain private witness"
end Minidregg.Host.BendCommitmentIR2Emit

def main (args : List String) : IO Unit := do
  let [privatePath, directory] := args |
    throw (IO.userError "usage: BendCommitmentIR2Emit private-preimage-file fixture-directory")
  Minidregg.Host.BendCommitmentIR2Emit.emitFixture privatePath directory
