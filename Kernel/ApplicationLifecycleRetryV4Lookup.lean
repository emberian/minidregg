/-
Receipt-only lookup for the repeat-CREATE family: event69 BEGIN, event70
claim and event72 completion. The same verifier walk that admitted the
complete historical image supplies records and receipts; these selectors never
mint a launch reservation and never resubmit.
-/
import Kernel.NativeHostReplay

namespace Minidregg.Kernel.ApplicationLifecycleRetryV4Lookup

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
    (nullifiers : List Minidregg.Kernel.DurableDataIntent.StableNullifier) :
    Except Error (Option Receipt) := do
  let some index := verified.opened.durable.image.accepted.findIdx?
      (fun record => record.transactionId == transactionId)
    | .ok none
  let some record := verified.opened.durable.image.accepted[index]?
    | .error .nativeHistoryUnavailable
  let some receipt := verified.receipts[index]?
    | .error .nativeHistoryUnavailable
  if record.event == event && nullifiers.all record.nullifiers.contains &&
      receipt.transactionId == transactionId &&
      receipt.eventId == event.eventId && receipt.acceptedCount == index + 1 then
    .ok (some receipt)
  else .error .transactionConflict

def beginVerified {config : Config} {target : Durable}
    (verified : NativeHostReplay.Verified config target) (bytes : List UInt8) :
    Except Error (Option Receipt) := do
  let some ingress := ApplicationLifecycleRetryBeginV4Ingress.codec.decode bytes
    | .error .malformed
  let base := ingress.begin.base
  select verified base.transactionId
    (ApplicationLifecycleRetryBeginV4Admission.event ingress)
    [ApplicationLifecycleBegin.stableNullifier base.domain base.semantics base.source]

/-- A retry claim's receipt is returned only if its record also consumed the
one-use retry token of the exact recovery it names. -/
def claimVerified {config : Config} {target : Durable}
    (verified : NativeHostReplay.Verified config target) (bytes : List UInt8) :
    Except Error (Option Receipt) := do
  let some ingress := ApplicationLifecycleRetryClaimV4Ingress.codec.decode bytes
    | .error .malformed
  select verified ingress.base.transactionId
    (ApplicationLifecycleRetryClaimV4Core.event ingress)
    [ApplicationLifecycleClaim.stableNullifier ingress.base.domain
      ingress.base.semantics ingress.base.source, ingress.retryToken]

def completionVerified {config : Config} {target : Durable}
    (verified : NativeHostReplay.Verified config target) (bytes : List UInt8) :
    Except Error (Option Receipt) := do
  let some ingress := ApplicationLifecycleRetryCompletionV4Ingress.codec.decode bytes
    | .error .malformed
  let transactionId := DeclaredResourceController.transactionId ingress.domain
    ingress.semantics (ingress.source.command ingress.domain ingress.semantics)
  let creation := match ingress.creationMarker with
    | none => []
    | some marker => [marker]
  select verified transactionId
    (ApplicationLifecycleRetryCompletionV4Ingress.event ingress)
    (ApplicationLifecycleRetryCompletionV4Ingress.stableNullifier ingress :: creation)

end Minidregg.Kernel.ApplicationLifecycleRetryV4Lookup
