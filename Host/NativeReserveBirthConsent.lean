/- Dedicated full-peer reserve-birth consent adapter. This source remains WIP
until its exact high authoring producer closure is qualified against the current
controller ABI. It is separate so missing monetary rendering producers cannot
remove consent for independently qualified lifecycle and recovery families. -/
import Kernel.NativeHostReplay
import Host.NativeReserveBirthAuthoring
import Compiler.FnEvidenceCodec

namespace Minidregg.Host.NativeReserveBirthConsent
open Minidregg.Compiler Minidregg.Kernel
set_option autoImplicit false

def expectedPlanBytes (config : NativeHost.Config) {target : NativeHost.Durable}
    (verified : NativeHostReplay.Verified config target)
    (request : List UInt8) : IO (List UInt8) := do
  unless request.length ≤ FnEvidenceCodec.maxHostFrameBytes do
    throw (IO.userError "local reserve birth request exceeds native frame bound")
  let bytes ← IO.ofExcept (← NativeReserveBirthAuthoring.authorWireLoaded
    config verified.opened request)
  unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
    throw (IO.userError "local reserve birth plan exceeds native frame bound")
  pure bytes
end Minidregg.Host.NativeReserveBirthConsent
