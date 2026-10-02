/- Exact operator-configuration compatibility for a closed legacy carry.
Profile descriptions omit some settings; comparing those descriptions alone
cannot establish that an upgrade retained birth bounds or evaluator selection.
All unknown configuration fields remain in this comparison and therefore fail
closed if added, removed, or changed. Numeric JSON values stay arbitrary-width. -/
import Lean

namespace Minidregg.Compiler.CarryConfiguration

open Lean
set_option autoImplicit false

/-- Only physical custody and independently configured carry administration
may differ. Checkpoint cadence does not change admission or logical history. -/
def physicalFields : List String :=
  ["storageBinary", "storageRoot", "signatureBinary", "checkpointKey",
   "checkpointEvery", "carryRegistry", "carryOperatorKey"]

private def semanticFields (value : Json) : Except String Json := do
  let fields ← value.getObj?
  pure (.obj (physicalFields.foldl (fun result name => result.erase name) fields))

/-- The frozen old profile admitted births at their exact authored height.
The target's new default slack must not silently broaden that interval.
An explicitly chosen future template change needs its own authorized carry. -/
def checkLegacy (source target : Json) : Except String Unit := do
  let _ ← source.getObj?
  let _ ← target.getObj?
  let oldSlack := (source.getObjVal? "birthSlack").toOption.getD (toJson (0 : Nat))
  let nextSlack ← target.getObjValAs? Nat "birthSlack"
  if oldSlack != toJson (0 : Nat) || nextSlack != 0 then
    throw "legacy carry requires unchanged exact-height birth admission"
  let old := source.setObjVal! "birthSlack" (toJson (0 : Nat))
  if (← semanticFields old) != (← semanticFields target) then
    throw "carry changes operator configuration beyond physical custody"

end Minidregg.Compiler.CarryConfiguration
