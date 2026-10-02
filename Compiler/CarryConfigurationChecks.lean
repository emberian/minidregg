import Compiler.CarryConfiguration

namespace Minidregg.Compiler.CarryConfigurationChecks
open Lean
open CarryConfiguration
set_option autoImplicit false

private def source : Json := Json.mkObj [
  ("domain", toJson (1 : Nat)),
  ("expectedSeed", toJson (123456789012345678901234567890123456789 : Nat)),
  ("disabledEvaluators", toJson (["nock"] : List String)),
  ("storageRoot", .str "/retained/source"),
  ("extension", .str "must remain bound")]
private def target : Json :=
  (source.setObjVal! "birthSlack" (toJson (0 : Nat))).setObjVal!
    "storageRoot" (.str "/isolated/target")
private def accepts (next : Json) : Bool :=
  match checkLegacy source next with
  | .ok () => true
  | .error _ => false

-- Relocation is permitted while all authority-affecting settings remain fixed.
#guard accepts target
-- A new default must not expand the old birth window.
#guard !accepts source
#guard !accepts (target.setObjVal! "birthSlack" (toJson (64 : Nat)))
-- Disabled evaluators and unknown extension settings remain in the gate.
#guard !accepts (target.setObjVal! "disabledEvaluators" (toJson ([] : List String)))
#guard !accepts (target.setObjVal! "extension" (.str "changed"))
-- Adjacent values far above IEEE754 integer precision remain distinguishable.
#guard !accepts (target.setObjVal! "expectedSeed"
  (toJson (123456789012345678901234567890123456788 : Nat)))

end Minidregg.Compiler.CarryConfigurationChecks
