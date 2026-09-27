/-
Receipt-only lookup for launch-bound event23 BEGIN and event24 claim. The same
verifier walk that admitted the complete historical image supplies records
and receipts; these selectors never mint a physical launch reservation.
-/
import Kernel.NativeHostReplay

namespace Minidregg.Kernel.ApplicationLifecycleV3Lookup

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

inductive Error where
  | malformed
  | transactionConflict
  | nativeHistoryUnavailable
  deriving DecidableEq, Repr

private def select {config : Config} {target : Durable}
    (verified : NativeHostReplay.Verified config target)
    (transactionId : Minidregg.Theory.TypedAuthorization.Digest)
    (event : Minidregg.Kernel.DurableDataIntent.StableEvent)
    (nullifier : Minidregg.Kernel.DurableDataIntent.StableNullifier) :
    Except Error (Option Receipt) := do
  let some index := verified.opened.durable.image.accepted.findIdx?
      (fun record => record.transactionId == transactionId)
    | .ok none
  let some record := verified.opened.durable.image.accepted[index]?
    | .error .nativeHistoryUnavailable
  let some receipt := verified.receipts[index]?
    | .error .nativeHistoryUnavailable
  if record.event == event && record.nullifiers.contains nullifier &&
      receipt.transactionId == transactionId &&
      receipt.eventId == event.eventId && receipt.acceptedCount == index + 1 then
    .ok (some receipt)
  else .error .transactionConflict

def beginVerified {config : Config} {target : Durable}
    (verified : NativeHostReplay.Verified config target) (bytes : List UInt8) :
    Except Error (Option Receipt) := do
  let some ingress := ApplicationLifecycleBeginV3Ingress.codec.decode bytes
    | .error .malformed
  select verified ingress.base.transactionId
    (ApplicationLifecycleBeginV3Ingress.event ingress)
    (ApplicationLifecycleBegin.stableNullifier ingress.base.domain
      ingress.base.semantics ingress.base.source)

def claimVerified {config : Config} {target : Durable}
    (verified : NativeHostReplay.Verified config target) (bytes : List UInt8) :
    Except Error (Option Receipt) := do
  let some ingress := ApplicationLifecycleClaimV3Ingress.codec.decode bytes
    | .error .malformed
  select verified ingress.base.transactionId
    (ApplicationLifecycleClaimV3Ingress.event ingress)
    (ApplicationLifecycleClaim.stableNullifier ingress.base.domain
      ingress.base.semantics ingress.base.source)


end Minidregg.Kernel.ApplicationLifecycleV3Lookup
