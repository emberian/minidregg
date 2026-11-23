/-
Receipt-only event26 recovery. An exact historical record can report its
receipt; lookup never mints another app delivery permit or resends fd3 bytes.
-/
module

public import Kernel.ApplicationAgentLifetimeDispatchProjection
public import Kernel.ApplicationAgentLifetimeGrantReceiver

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Kernel.ApplicationAgentLifetimeDispatchLookup

open Minidregg.Compiler
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

inductive Error where
  | malformed
  | transactionConflict
  | nativeHistoryUnavailable
  deriving DecidableEq, Repr

private def compareReceipt {config : Config} (ingress : ApplicationAgentLifetimeDispatchIngress.Ingress)
    (transactionId : Minidregg.Theory.TypedAuthorization.Digest) (index : Nat)
    (record : DurableReceiver.IntentRecord) (receipt : NativeHostCodec.Receipt)
    (grant : ApplicationAgentLifetimeGrant.Grant) (grantIndex reserveIndex : Nat)
    (raw : ApplicationDispatchAgentReserveCore.RawEvidence config) : Except Error (Option NativeHostCodec.Receipt) := do
  let .ok bound := ApplicationAgentLifetimeDispatchReserveCore.bindContext
      raw ingress.reserveContext
    | .error .transactionConflict
  let event := ApplicationAgentLifetimeDispatchIngress.event ingress
  let operation := ApplicationDispatchAdmissionIngress.nullifier ingress.dispatch
  let reserveClaim := ApplicationAgentLifetimeDispatchReserveCore.claimNullifier bound
  if ApplicationAgentLifetimeDispatchReserveContext.matchesGrant
        ingress.reserveContext grant grantIndex &&
      decide (grantIndex < reserveIndex) &&
      decide (reserveIndex < index) &&
      record.event == event && record.nullifiers.contains operation &&
      record.nullifiers.contains reserveClaim &&
      receipt.transactionId == transactionId &&
      receipt.eventId == event.eventId && receipt.acceptedCount == index + 1 then
    .ok (some receipt)
  else .error .transactionConflict

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
  let some index := verified.opened.durable.firstIndex (transactionId)
    | .ok none
  let some record := verified.opened.durable.image.accepted[index]?
    | .error .nativeHistoryUnavailable
  let some receipt := verified.receiptAt index
    | .error .nativeHistoryUnavailable
  let some grant := verified.grants.find?
      (fun prior => prior.index == ingress.reserveContext.grantIssueIndex)
    | .error .transactionConflict
  let some reserve := verified.reserves.find?
      (fun prior => prior.index == ingress.reserveIndex)
    | .error .transactionConflict
  compareReceipt ingress transactionId index record receipt grant.ingress.spec.grant grant.index reserve.index reserve.raw

/-- Receipt-only recovery reads the original transaction, grant, ticket and reserve under one head. -/
def lookupLight {config : Config} (light : NativeHostLight.Light config) (bytes : List UInt8) :
    ExceptT Error IO (Option NativeHostCodec.Receipt) := do
  let some ingress := ApplicationAgentLifetimeDispatchIngress.codec.decode bytes | throw .malformed
  let some selection := ApplicationDispatchAdmission.selectCommand ingress.dispatch | throw .malformed
  let command := ApplicationDispatchCommand.command ingress.dispatch.dispatch selection ingress.dispatch.parent
  let tx := DeclaredResourceController.transactionId ingress.dispatch.dispatch.domain ingress.dispatch.dispatch.semantics command
  let reader := light.opening.reader config.transport ResourceBirthCodec.rootBytes
  let historyError : NativeHostReplay.IssueRefusal → Error
    | .history _ => .nativeHistoryUnavailable
    | .refused _ => .transactionConflict
  match ← ExceptT.mk ((·.mapError (fun _ => Error.nativeHistoryUnavailable)) <$> reader.byTx tx) with
  | .absent _ => return none
  | .present found =>
    let grant ← ExceptT.mk ((·.mapError historyError) <$>
      (ApplicationAgentLifetimeGrantReceiver.selectGrant config light ingress.reserveContext.grantIssueIndex).run)
    let raw ← ExceptT.mk ((·.mapError historyError) <$> (NativeHostReplay.selectReserve config reader ingress.reserveIndex).run)
    compareReceipt ingress tx (found.height - 1) found.read.record (receiptOfRecord found.read)
      grant.ingress.spec.grant ingress.reserveContext.grantIssueIndex ingress.reserveIndex raw

def lookupOriginal (config : Config) (target : Durable) (bytes : List UInt8) :
    IO (Except Error (Option NativeHostCodec.Receipt)) := do
  let ⟨_, reader⟩ ← match ← DurableHistoryStore.readerOf config.transport ResourceBirthCodec.rootBytes target with
    | .error _ => return .error .nativeHistoryUnavailable
    | .ok reader => pure reader
  let .ok verified ← NativeHostReplay.verifyStart config reader target
    | return .error .nativeHistoryUnavailable
  return lookupVerified verified bytes

end Minidregg.Kernel.ApplicationAgentLifetimeDispatchLookup
