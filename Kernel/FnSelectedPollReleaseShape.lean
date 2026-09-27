/-
Exact event13 historical shape used by the selected fn gateway testimony. This
is a lower component check, not proof that a caller's record was admitted.
Replay supplies the record and receipt from its same native-admitted walk;
the upper live selector supplies them from a private Verified value.
-/
import Kernel.FnSelectiveReleaseReceiver

namespace Minidregg.Kernel.FnSelectedPollReleaseShape

open Minidregg.Kernel
open Minidregg.Kernel.FnSelectiveReleaseIngress
open Minidregg.Compiler

set_option autoImplicit false

structure Original where
  ingress : FnSelectiveReleaseIngress.Ingress
  receipt : NativeHostCodec.Receipt

def selectAt (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (record : DurableReceiver.IntentRecord) (receipt : NativeHostCodec.Receipt)
    (releaseKey : Minidregg.Theory.TypedAuthorization.Digest) : Option Original := do
  if record.event.codecVersion != 13 ||
      record.transactionId != releaseKey ||
      receipt.transactionId != record.transactionId ||
      receipt.eventId != record.event.eventId then none else
  let ingress ← ingressCodec.decode record.event.canonicalBytes
  if transactionId ingress != releaseKey ||
      event ingress != record.event ||
      FnSelectiveReleaseReceiver.replay config opened ingress !=
        some (.ok (FnSelectiveReleaseReceiver.receipt ingress)) then
    none
  else some ⟨ingress, receipt⟩

end Minidregg.Kernel.FnSelectedPollReleaseShape
