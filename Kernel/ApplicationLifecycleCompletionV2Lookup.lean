/-
Receipt-only lookup of a previously admitted v2 checked completion. An exact
historical receipt cannot run a physical host effect or create a new event.
-/
import Kernel.ApplicationLifecycleCompletionV2Core
import Kernel.NativeHostReplay

namespace Minidregg.Kernel.ApplicationLifecycleCompletionV2Lookup

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
  let some ingress := ApplicationLifecycleCompletionV2Ingress.codec.decode bytes
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
  let event := ApplicationLifecycleCompletionV2Ingress.event ingress
  let reportNullifier := ApplicationLifecycleCompletionV2Ingress.stableNullifier ingress
  let creationExact := match ingress.creationMarker with
    | none => true
    | some marker => record.nullifiers.contains marker
  if record.event == event && record.nullifiers.contains reportNullifier && creationExact &&
      receipt.transactionId == transactionId &&
      receipt.eventId == event.eventId && receipt.acceptedCount == index + 1 then
    .ok (some receipt)
  else .error .transactionConflict

end Minidregg.Kernel.ApplicationLifecycleCompletionV2Lookup
