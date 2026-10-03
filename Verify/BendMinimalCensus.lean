import Assurance.BendObliviousMinimal
import Compiler.PrivateCircuitAllocationFast
open Minidregg.Assurance.BendObliviousMinimal


/-- Public graph census: XOR is local, AND advances one dependency layer. -/
def andLayerHistogram (network : Minidregg.Compiler.ObliviousNetwork.Network) : Array (Nat × Nat) := Id.run do
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
  pure ((layers.toList.zipIdx).filterMap fun (count,level) =>
    if count == 0 then none else some (level,count)).toArray

def main : IO Unit := do
  match prepare with
  | none => throw (IO.userError "admitted full controller refused")
  | some input =>
    IO.println s!"CENSUS {repr input.prepared.network.census}"
    (← IO.getStdout).flush
    let histogram := andLayerHistogram input.prepared.network
    IO.println s!"AND_LAYERS {repr histogram}"
    if histogram.foldl (fun total p => total + p.2) 0 != input.prepared.network.census.ands then
      throw (IO.userError "AND histogram total disagrees with actual census")
    IO.println s!"NETWORK_BYTES {(Minidregg.Compiler.PrivateCircuitAllocationFast.encodeNetwork input.prepared.network).length}"
    (← IO.getStdout).flush
    let rows := (List.range (ticks * input.prepared.network.census.ands)).map fun index =>
      (⟨⟨42⟩,index⟩ : Minidregg.Kernel.PrivateSuccessorCustody.CorrelationId)
    let plan : Minidregg.Compiler.PrivateCircuitAllocation.Plan :=
      ⟨⟨⟨0⟩,[3],7,11,⟨0⟩⟩,input.prepared.network,ticks,[9],rows⟩
    let encoded := Minidregg.Compiler.PrivateCircuitAllocationFast.encodePlan plan
    IO.println s!"ENCODED_PLAN {encoded.length}"
    (← IO.getStdout).flush
    let parsedPrefix := Minidregg.Compiler.PrivateCircuitAllocationFast.fastFramedPlanStream.decodePrefix encoded
    IO.println s!"PREFIX_ROWS {repr (parsedPrefix.map fun p => p.1.rows.length)}"
    (← IO.getStdout).flush
    let decoded := Minidregg.Compiler.PrivateCircuitAllocationFast.decodePlan encoded
    IO.println s!"PLAN_BYTES {encoded.length} ROWS {rows.length} DECODE_ROWS {repr (decoded.map fun p => p.rows.length)}"
    let extra := Minidregg.Compiler.PrivateCircuitAllocationFast.decodePlan (encoded ++ [0])
    let wrongFrame := Minidregg.Compiler.PrivateCircuitAllocationFast.decodePlan (encoded.set 3 0)
    IO.println s!"CANONICAL_REJECT trailing={extra.isNone} wrongFrame={wrongFrame.isNone}"
    if !extra.isNone || !wrongFrame.isNone then throw (IO.userError "canonical rejection failed")
    IO.println s!"INPUT {input.bits.size} TICKS {ticks} OBSERVE {repr observe}"
