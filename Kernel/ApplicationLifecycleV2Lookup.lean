/-
Receipt-only lookup for descriptor-bound lifecycle BEGIN and claim. The same
verifier walk that admitted the complete historical image supplies records
and receipts; these selectors never mint a physical launch reservation.
-/
import Kernel.NativeHostReplay

namespace Minidregg.Kernel.ApplicationLifecycleV2Lookup

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
  let some ingress := ApplicationLifecycleBeginV2Ingress.codec.decode bytes
    | .error .malformed
  select verified ingress.base.transactionId
    (ApplicationLifecycleBeginV2Ingress.event ingress)
    (ApplicationLifecycleBegin.stableNullifier ingress.base.domain
      ingress.base.semantics ingress.base.source)

def claimVerified {config : Config} {target : Durable}
    (verified : NativeHostReplay.Verified config target) (bytes : List UInt8) :
    Except Error (Option Receipt) := do
  let some ingress := ApplicationLifecycleClaimV2Ingress.codec.decode bytes
    | .error .malformed
  select verified ingress.base.transactionId
    (ApplicationLifecycleClaimV2Ingress.event ingress)
    (ApplicationLifecycleClaim.stableNullifier ingress.base.domain
      ingress.base.semantics ingress.base.source)

/-- Existing v1 records are readable by exact receipt only. A v1 lookup is
never a fresh BEGIN or claim permit for a signed-SPK host. -/
def beginLegacyVerified {config : Config} {target : Durable}
    (verified : NativeHostReplay.Verified config target) (bytes : List UInt8) :
    Except Error (Option Receipt) := do
  let some ingress := ApplicationLifecycleBeginIngress.codec.decode bytes
    | .error .malformed
  select verified ingress.transactionId
    (ApplicationLifecycleBeginIngress.event ingress)
    (ApplicationLifecycleBegin.stableNullifier ingress.domain
      ingress.semantics ingress.source)

def claimLegacyVerified {config : Config} {target : Durable}
    (verified : NativeHostReplay.Verified config target) (bytes : List UInt8) :
    Except Error (Option Receipt) := do
  let some ingress := ApplicationLifecycleClaimIngress.codec.decode bytes
    | .error .malformed
  select verified ingress.transactionId
    (ApplicationLifecycleClaimIngress.event ingress)
    (ApplicationLifecycleClaim.stableNullifier ingress.domain
      ingress.semantics ingress.source)

end Minidregg.Kernel.ApplicationLifecycleV2Lookup
