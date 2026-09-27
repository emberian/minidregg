/-
Receipt-only lookup of a previously admitted checked completion. An exact
historical receipt cannot run a physical host effect or create a new event.
-/
import Kernel.ApplicationLifecycleCompletionReceiver

namespace Minidregg.Kernel.ApplicationLifecycleCompletionLookup

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

inductive Error where
  | malformed
  | transactionConflict
  | nativeHistoryUnavailable
  deriving DecidableEq, Repr

def verified {config : Config} {target : Durable}
    (tip : NativeHostReplay.Verified config target) (bytes : List UInt8) :
    Except Error (Option Receipt) := do
  let some ingress := ApplicationLifecycleCompletionIngress.codec.decode bytes
    | .error .malformed
  let transactionId := DeclaredResourceController.transactionId ingress.domain
    ingress.semantics (ingress.source.command ingress.domain ingress.semantics)
  let some index := tip.opened.durable.image.accepted.findIdx?
      (fun record => record.transactionId == transactionId)
    | .ok none
  let some record := tip.opened.durable.image.accepted[index]?
    | .error .nativeHistoryUnavailable
  let some receipt := tip.receipts[index]?
    | .error .nativeHistoryUnavailable
  let event := ApplicationLifecycleCompletionIngress.event ingress
  let reportNullifier := ApplicationLifecycleCompletionIngress.stableNullifier ingress
  if record.event == event && record.nullifiers.contains reportNullifier &&
      receipt.transactionId == transactionId &&
      receipt.eventId == event.eventId && receipt.acceptedCount == index + 1 then
    .ok (some receipt)
  else .error .transactionConflict

end Minidregg.Kernel.ApplicationLifecycleCompletionLookup
