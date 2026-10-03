/- Exact JSON boundary consumed by the generic native Surface adapter. This
serializes only decoded typed source output; admitted observations, accepted
origin, operation custody and links are independent receiver inputs. -/
import Compiler.BendSurfaceLowering
import Lean

namespace Minidregg.Host.BendSurfaceJson
open Minidregg.Compiler.BendWorldSurface
open Minidregg.Compiler.Tower256ConcreteBackend
open Lean
set_option autoImplicit false

private def decimal (value : Nat) : Json := .str (toString value)
private def digest (value : Digest) : Json := decimal value.value
private def hexDigit (value : Nat) : Char :=
  Char.ofNat (if value < 10 then 48 + value else 87 + value)
def hex (bytes : List UInt8) : String := String.ofList (bytes.flatMap fun byte =>
  [hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)])

def intent (value : Intent) : Json := Json.mkObj
  [("artifact", digest value.artifact), ("exportName", .str value.exportName),
   ("program", digest value.program), ("instance", decimal value.«instance»),
   ("expectedRoot", digest value.expectedRoot), ("arguments", .str (hex value.arguments))]
def node (value : Node) : Json := Json.mkObj
  [("tag", decimal value.tag), ("slot", decimal value.slot), ("label", .str value.label),
   ("children", .arr (value.children.map decimal).toArray)]
def surface (value : Surface) : Json := Json.mkObj
  [("artifact", digest value.artifact), ("exportName", .str value.exportName),
   ("nodes", .arr (value.nodes.map node).toArray), ("root", decimal value.root),
   ("intents", .arr (value.intents.map intent).toArray)]

/-- Only the actual decoded output witness is accepted at this bridge. The
expected origin and observation count are independent native receiving inputs.
This function deliberately adds no observations, enabled flags or URLs. -/
def evaluated {core : Minidregg.Compiler.BendCoreAdmission.Checked}
    {initial : Minidregg.Theory.BendTT.Term} {artifact : Digest}
    {exportName : String} {observationCount : Nat}
    (value : Minidregg.Compiler.BendSurfaceLowering.Evaluated
      core initial artifact exportName observationCount) : Json := surface value.surface

end Minidregg.Host.BendSurfaceJson
