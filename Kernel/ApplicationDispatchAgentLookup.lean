/-
Receipt-only recovery for event21. A retained paid-dispatch record confirms
history; it never authorizes another fd3 send or creates a fresh permit.
-/
module

public import Kernel.ApplicationDispatchAgentReceiver
public import Kernel.ApplicationDispatchAdmission
public import Kernel.NativeHost

@[expose] public section

namespace Minidregg.Kernel.ApplicationDispatchAgentLookup

open Minidregg.Compiler
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

inductive Error where
  | malformed
  | transactionConflict
  | nativeHistoryUnavailable
  deriving DecidableEq, Repr

private def compareReceipt {config : Config} (ingress : ApplicationDispatchAgentIngress.Ingress)
    (transactionId : Minidregg.Theory.TypedAuthorization.Digest) (index : Nat)
    (record : DurableReceiver.IntentRecord) (receipt : NativeHostCodec.Receipt)
    (raw : ApplicationDispatchAgentReserveCore.RawEvidence config) : Except Error (Option NativeHostCodec.Receipt) := do
  let .ok bound := raw.bindContext ingress.reserveContext | .error .transactionConflict
  let event := ApplicationDispatchAgentIngress.event ingress
  let nullifier := ApplicationDispatchAdmissionIngress.nullifier ingress.dispatch
  let claim := ApplicationDispatchAgentReserveCore.claimNullifier bound
  if record.event == event && record.nullifiers.contains nullifier &&
      record.nullifiers.contains claim &&
      receipt.transactionId == transactionId &&
      receipt.eventId == event.eventId && receipt.acceptedCount == index + 1 then
    .ok (some receipt)
  else .error .transactionConflict

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
  let some index := verified.opened.durable.firstIndex (transactionId)
    | .ok none
  let some record := verified.opened.durable.image.accepted[index]?
    | .error .nativeHistoryUnavailable
  let some receipt := verified.receiptAt index
    | .error .nativeHistoryUnavailable
  let some reserve := verified.reserves.find? (fun reserve =>
      reserve.index == ingress.reserveIndex)
    | .error .transactionConflict
  compareReceipt ingress transactionId index record receipt reserve.raw

/-- Receipt recovery over authenticated transaction and reserve selections at one head. -/
def lookupLight {config : Config} (light : NativeHostLight.Light config) (bytes : List UInt8) :
    ExceptT Error IO (Option NativeHostCodec.Receipt) := do
  let some ingress := ApplicationDispatchAgentIngress.codec.decode bytes | throw .malformed
  let some selection := ApplicationDispatchAdmission.selectCommand ingress.dispatch | throw .malformed
  let command := ApplicationDispatchCommand.command ingress.dispatch.dispatch selection ingress.dispatch.parent
  let transactionId := DeclaredResourceController.transactionId ingress.dispatch.dispatch.domain
    ingress.dispatch.dispatch.semantics command
  let reader := light.opening.reader config.transport ResourceBirthCodec.rootBytes
  match ← ExceptT.mk ((·.mapError (fun _ => Error.nativeHistoryUnavailable)) <$> reader.byTx transactionId) with
  | .absent _ => return none
  | .present found =>
    let raw ← ExceptT.mk ((·.mapError (fun
      | .history _ => Error.nativeHistoryUnavailable
      | .refused _ => Error.transactionConflict)) <$> (NativeHostReplay.selectReserve config reader ingress.reserveIndex).run)
    compareReceipt ingress transactionId (found.height - 1) found.read.record (receiptOfRecord found.read) raw

def lookupOriginal (config : Config) (target : Durable) (bytes : List UInt8) :
    IO (Except Error (Option NativeHostCodec.Receipt)) := do
  let ⟨_, reader⟩ ← match ← DurableHistoryStore.readerOf config.transport ResourceBirthCodec.rootBytes target with
    | .error _ => return .error .nativeHistoryUnavailable
    | .ok reader => pure reader
  let .ok verified ← NativeHostReplay.verifyStart config reader target
    | return .error .nativeHistoryUnavailable
  return lookupVerified verified bytes

end Minidregg.Kernel.ApplicationDispatchAgentLookup
