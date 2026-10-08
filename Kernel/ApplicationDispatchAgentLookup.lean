/-
Receipt-only recovery for event21. A retained paid-dispatch record confirms
history; it never authorizes another fd3 send or creates a fresh permit.
-/
import Kernel.ApplicationDispatchAgentReceiver
import Kernel.ApplicationDispatchAdmission

namespace Minidregg.Kernel.ApplicationDispatchAgentLookup

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
  let some ingress := ApplicationDispatchAgentIngress.codec.decode bytes
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
  let some reserve := verified.reserves.find? (fun reserve =>
      reserve.index == ingress.reserveIndex)
    | .error .transactionConflict
  let .ok bound := reserve.raw.bindContext ingress.reserveContext
    | .error .transactionConflict
  let event := ApplicationDispatchAgentIngress.event ingress
  let nullifier := ApplicationDispatchAdmissionIngress.nullifier ingress.dispatch
  let claim := ApplicationDispatchAgentReserveCore.claimNullifier bound
  if record.event == event && record.nullifiers.contains nullifier &&
      record.nullifiers.contains claim &&
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

end Minidregg.Kernel.ApplicationDispatchAgentLookup
