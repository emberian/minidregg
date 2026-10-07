/- The declared envelope's JSON surface, ONE definition: the eighteen
`ObjectiveInvocationClaim.Capacity` lanes as decimal strings, decoded
(`capacity`) and encoded (`capacityJson`), with the field readers every Host
JSON authoring module shares. `Host.SeatJson` and `Host.ObjectiveActivityJson`
both author signed commands whose envelopes are this object; neither keeps a
copy.

Nothing here decides anything: an envelope is judged by the kernel that
covers it (`Config.covers`). -/
import Compiler.ObjectiveInvocationClaim
import Lean.Data.Json

namespace Minidregg.Host.CapacityJson
open Lean (Json toJson)
open Minidregg.Compiler.ObjectiveInvocationClaim (Capacity)
set_option autoImplicit false

abbrev Result := Except String

def decimal (value : Nat) : Json := .str (toString value)

def field (path : String) (json : Json) (name : String) : Result Json :=
  match json.getObjVal? name with
  | .ok value => .ok value
  | .error _ => .error s!"{path}.{name} missing"

/-- A canonical decimal string (no sign, no leading zero, no whitespace). -/
def natOf (path : String) (value : Json) : Result Nat := do
  let some text := value.getStr?.toOption | throw s!"{path} must be a decimal string"
  let some n := text.toNat? | throw s!"{path} must be a decimal string"
  unless toString n == text do throw s!"{path} must be canonical decimal"
  pure n

def nat (path : String) (json : Json) (name : String) : Result Nat := do
  natOf s!"{path}.{name}" (← field path json name)

/-- A declared envelope: the eighteen `Capacity` lanes as decimal strings. -/
def capacity (path : String) (json : Json) : Result Capacity := do
  let n := nat path json
  pure ⟨← n "typeFuel", ← n "sourceTicks", ← n "heap", ← n "stack", ← n "outputNodes", ← n "outputBytes",
    ← n "inputBytes", ← n "scalarBits", ← n "memoryTouches", ← n "proofWork", ← n "feeDebit", ← n "turnBytes",
    ← n "witnessBytes", ← n "storageBytes", ← n "sideEffectCount", ← n "networkBytes", ← n "leaseByteBlocks",
    ← n "incidences"⟩

def capacityJson (c : Capacity) : Json := .mkObj
  [("typeFuel", decimal c.typeFuel), ("sourceTicks", decimal c.sourceTicks), ("heap", decimal c.heap),
   ("stack", decimal c.stack), ("outputNodes", decimal c.outputNodes), ("outputBytes", decimal c.outputBytes),
   ("inputBytes", decimal c.inputBytes), ("scalarBits", decimal c.scalarBits),
   ("memoryTouches", decimal c.memoryTouches), ("proofWork", decimal c.proofWork), ("feeDebit", decimal c.feeDebit),
   ("turnBytes", decimal c.turnBytes), ("witnessBytes", decimal c.witnessBytes),
   ("storageBytes", decimal c.storageBytes), ("sideEffectCount", decimal c.sideEffectCount),
   ("networkBytes", decimal c.networkBytes), ("leaseByteBlocks", decimal c.leaseByteBlocks),
   ("incidences", decimal c.incidences)]

end Minidregg.Host.CapacityJson
