/- Public interoperability fixture for the actual canonical Plan codec.
No secret material, production state or release authority is embedded here. -/
import Compiler.PrivateCircuitAllocation
import Lean

namespace Minidregg.Host.PrivateCircuitPlanFixture
open Minidregg.Compiler.PrivateCircuitAllocation
open Minidregg.Kernel.PrivateSuccessorCustody

def plan : Plan :=
  { generation := ⟨⟨0⟩, [3], 7, 11, ⟨0⟩⟩
    network := ⟨2, #[.xor 0 1, .and 0 2], #[3]⟩
    publicTicks := 2
    bindingBytes := [9]
    rows := [⟨⟨42⟩, 0⟩, ⟨⟨42⟩, 1⟩] }

end Minidregg.Host.PrivateCircuitPlanFixture

def main : IO Unit := do
  let plan := Minidregg.Host.PrivateCircuitPlanFixture.plan
  let bytes := Minidregg.Compiler.PrivateCircuitAllocation.encode plan
  IO.println (Lean.Json.mkObj [
    ("valid", toJson plan.valid),
    ("bytes", toJson (bytes.map UInt8.toNat)),
    ("schedule", toJson (Minidregg.Compiler.PrivateCircuitAllocation.schedule plan)),
    ("rowCount", toJson plan.rows.length)]).compress
