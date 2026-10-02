/- Shared source recommendation for useful paid entry. Provider tokens and
compute are separately priced. A byte-priced deployment needs an explicit
budget because these fixed interaction counts cannot quote unknown bytes. -/
import Theory.ResourceBirth

namespace Minidregg.Kernel.PayStarterAllowance
open Minidregg.Theory.ResourceBirth (CreationTariff)
set_option autoImplicit false

def recommendation (tariff : CreationTariff) (renewal : Bool) : Option Nat :=
  if renewal then some 0
  else if tariff.perInitialPayloadByte = 0 then
    some (105 * tariff.base + 8 * tariff.perBirth + 16 * tariff.perGrant)
  else none

end Minidregg.Kernel.PayStarterAllowance
