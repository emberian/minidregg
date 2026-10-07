/-
Receipt-only event26 recovery. An exact historical record can report its
receipt; lookup never mints another app delivery permit or resends fd3 bytes.
-/
import Kernel.ApplicationAgentLifetimeDispatchProjection

namespace Minidregg.Kernel.ApplicationAgentLifetimeDispatchLookup

open Minidregg.Compiler
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

inductive Error where
  | malformed
  | transactionConflict
  | nativeHistoryUnavailable
  deriving DecidableEq, Repr

def lookupVerified {config : Config} {target : Durable}
    (verified : NativeHostReplay.Verified config target) (bytes : List UInt8) :
    Except Error (Option NativeHostCodec.Receipt) := do
  let some ingress := ApplicationAgentLifetimeDispatchIngress.codec.decode bytes
    | .error .malformed
  let some selection := ApplicationDispatchAdmission.selectCommand ingress.dispatch
    | .error .malformed
  let command := ApplicationDispatchCommand.command ingress.dispatch.dispatch
    selection ingress.dispatch.parent
  let transactionId := DeclaredResourceController.transactionId
    ingress.dispatch.dispatch.domain ingress.dispatch.dispatch.semantics command
  let some index := verified.opened.durable.image.accepted.findIdx?
      (fun record => record.transactionId == transactionId)
    | .ok none
  let some record := verified.opened.durable.image.accepted[index]?
    | .error .nativeHistoryUnavailable
  let some receipt := verified.receipts[index]?
    | .error .nativeHistoryUnavailable
  let some grant := verified.grants.find?
      (fun prior => prior.index == ingress.reserveContext.grantIssueIndex)
    | .error .transactionConflict
  let some reserve := verified.reserves.find?
      (fun prior => prior.index == ingress.reserveIndex)
    | .error .transactionConflict
  let .ok bound := ApplicationAgentLifetimeDispatchReserveCore.bindContext
      reserve.raw ingress.reserveContext
    | .error .transactionConflict
  let event := ApplicationAgentLifetimeDispatchIngress.event ingress
  let operation := ApplicationDispatchAdmissionIngress.nullifier ingress.dispatch
  let reserveClaim := ApplicationAgentLifetimeDispatchReserveCore.claimNullifier bound
  if ApplicationAgentLifetimeDispatchReserveContext.matchesGrant
        ingress.reserveContext grant.ingress.spec.grant grant.index &&
      decide (grant.index < reserve.index) &&
      decide (reserve.index < index) &&
      record.event == event && record.nullifiers.contains operation &&
      record.nullifiers.contains reserveClaim &&
      receipt.transactionId == transactionId &&
      receipt.eventId == event.eventId && receipt.acceptedCount == index + 1 then
    .ok (some receipt)
  else .error .transactionConflict

def lookupOriginal (config : Config) (target : Durable) (bytes : List UInt8) :
    IO (Except Error (Option NativeHostCodec.Receipt)) := do
  let ⟨_, reader⟩ ← match ← DurableHistoryStore.readerOf config.transport ResourceBirthCodec.rootBytes target with
    | .error _ => return .error .nativeHistoryUnavailable
    | .ok reader => pure reader
  let .ok verified ← NativeHostReplay.verifyLoaded config reader target
    | return .error .nativeHistoryUnavailable
  return lookupVerified verified bytes

end Minidregg.Kernel.ApplicationAgentLifetimeDispatchLookup
