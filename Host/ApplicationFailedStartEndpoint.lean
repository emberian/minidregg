/- Exact current-law failed-START recovery endpoint. Native custody observes the
OS; this source boundary admits the historical claim, current authenticated law,
signed dead-incarnation evidence and exact durable state transition. -/
import Host.ApplicationFailedStartRecoveryAuthoring
import Host.ApplicationFailedStartRecoveryTools
import Kernel.ApplicationFailedStartRecoveryReceiver
import Kernel.ApplicationFailedStartRecoveryLookup

namespace Minidregg.Host.ApplicationFailedStartEndpoint
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Kernel
open Minidregg.Kernel.NativeHost
set_option autoImplicit false

abbrev prepare := ApplicationFailedStartRecoveryAuthoring.prepareRequestVerified
abbrev assemble := ApplicationFailedStartRecoveryAuthoring.assemble
abbrev submit := ApplicationFailedStartRecoveryReceiver.receiveVerified

def lookup {config : Config} {target : Durable}
    (verified : NativeHostReplay.Verified config target) (bytes : List UInt8) : Outcome :=
  match ApplicationFailedStartRecoveryLookup.verified verified bytes with
  | .ok none => .absent
  | .ok (some receipt) => .confirmed .replayed receipt
  | .error .malformed => .refused .malformed "failed-start-recovery".toUTF8.toList
      "noncanonical recovery ingress".toUTF8.toList
  | .error .transactionConflict => .refused .conflict "failed-start-recovery".toUTF8.toList
      "exact recovery ingress/receipt conflict".toUTF8.toList
  | .error .nativeHistoryUnavailable => .uncertain
      "original failed START recovery receipt unavailable".toUTF8.toList

end Minidregg.Host.ApplicationFailedStartEndpoint
