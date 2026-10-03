import Assurance.BendObliviousMinimal
import Compiler.ObliviousUnroll
open Minidregg.Assurance.BendObliviousMinimal
open Minidregg.Compiler

def andLayerHistogram (network : ObliviousNetwork.Network) : Array (Nat × Nat) := Id.run do
  let mut depth := Array.replicate network.inputCount 0
  let mut layers := Array.replicate (network.gates.size + 1) 0
  for gate in network.gates do
    let level := match gate with
      | .constant _ => 0
      | .xor left right => max (depth[left]?.getD 0) (depth[right]?.getD 0)
      | .and left right => 1 + max (depth[left]?.getD 0) (depth[right]?.getD 0)
    depth := depth.push level
    match gate with
    | .and _ _ => layers := layers.set! level (layers[level]?.getD 0 + 1)
    | _ => pure ()
  pure ((layers.toList.zipIdx).filterMap fun (count, level) =>
    if count == 0 then none else some (level, count)).toArray

def main : IO Unit := do
  let some input := prepare | throw (IO.userError "admitted controller refused")
  let graph := (ObliviousUnroll.build input.prepared.network ticks).network
  let histogram := andLayerHistogram graph
  if histogram.foldl (fun total p => total + p.2) 0 != graph.census.ands then
    throw (IO.userError "actual AND census mismatch")
  IO.println s!"CENSUS {repr graph.census}"
  IO.println s!"AND_LAYERS {repr histogram}"
  IO.println s!"AIR_BOOLEANITY_CONSTRAINTS {graph.inputCount + graph.gates.size}"
