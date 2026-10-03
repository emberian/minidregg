/- Actual canonical shared-network Plan producer for the width-two arithmetic
receiving experiment. Generation/binding are EXPLICIT SYNTHETIC values, never
world authority or a new Objective source-method execution receipt. -/
import Compiler.ObliviousNatAddSemantics
import Compiler.PrivateCircuitAllocationFast
namespace Minidregg.Host.ObliviousNatAddEmit
open Minidregg.Compiler.ObliviousNatAdd
open Minidregg.Compiler.PrivateCircuitAllocation
open Minidregg.Kernel.PrivateSuccessorCustody
set_option autoImplicit false

def plan : Plan :=
  let graph := additionNetwork 2
  let rows := (List.range (andPositions graph).length).map fun index =>
    (⟨⟨42⟩,index⟩ : CorrelationId)
  ⟨⟨⟨0⟩,[3],7,11,⟨0⟩⟩,graph,1,[9],rows⟩

theorem plan_valid : plan.valid = true := by
  simp only [plan, Minidregg.Compiler.ObliviousNatAddSemantics.additionNetwork2_shape]
  simp [Plan.valid, Minidregg.Compiler.ObliviousNetwork.Network.valid,
    andPositions,
    Minidregg.Compiler.ObliviousNetwork.Op.fits]
  apply List.Nodup.map
  · intro left right same
    exact congrArg CorrelationId.row same
  · exact List.nodup_range
#assert_axioms plan_valid
end Minidregg.Host.ObliviousNatAddEmit

def main (arguments : List String) : IO UInt32 := do
  let [output] := arguments | do
    IO.eprintln "usage: oblivious-nat-add-emit OWNED_PLAN_BIN"
    return 2
  let plan := Minidregg.Host.ObliviousNatAddEmit.plan
  let encoded := Minidregg.Compiler.PrivateCircuitAllocationFast.encodePlan plan
  if !plan.valid then throw (IO.userError "actual addition Plan shape refused")
  let decoded := Minidregg.Compiler.PrivateCircuitAllocationFast.decodePlan encoded
  if decoded.isNone then throw (IO.userError "canonical Plan roundtrip refused")
  if !(Minidregg.Compiler.PrivateCircuitAllocationFast.decodePlan (encoded++[0])).isNone then
    throw (IO.userError "canonical trailing-byte refusal failed")
  IO.FS.writeBinFile output ⟨encoded.toArray⟩
  IO.println (Lean.Json.mkObj [("schema",Lean.toJson "dregg.oblivious-nat-add.census.v1"),
    ("width",Lean.toJson 2),("inputs",Lean.toJson plan.network.inputCount),
    ("outputs",Lean.toJson plan.network.outputs.toList),
    ("gates",Lean.toJson plan.network.gates.size),("ands",Lean.toJson plan.network.census.ands),
    ("planBytes",Lean.toJson encoded.length),("ticks",Lean.toJson plan.publicTicks),
    ("binding",Lean.toJson "synthetic generation/binding; source/world authority absent")]).compress
  return 0
