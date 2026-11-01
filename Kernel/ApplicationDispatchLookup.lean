/-
Read-only original-receipt lookup for a special dispatch transaction. It
returns status only: a past receipt cannot be converted into a fresh physical
HTTP delivery permit, regardless of whether the request bytes repeat.
-/
module

public import Kernel.NativeHost
public import Kernel.ApplicationDispatchAdmission

@[expose] public section

namespace Minidregg.Kernel.ApplicationDispatchLookup

open Minidregg.Compiler
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

inductive Error where
  | malformed
  | transactionConflict
  | nativeHistoryUnavailable
  deriving DecidableEq, Repr

/-- Warm status lookup uses only the verifier-minted accepted image and its
same-walk receipt list. It never re-admits a past request under current law,
nor does it construct a physical delivery permit. -/
def lookupVerified {config : Config} {target : Durable}
    (verified : NativeHostReplay.Verified config target) (bytes : List UInt8) :
    Except Error (Option NativeHostCodec.Receipt) := do
  let some ingress := ApplicationDispatchAdmissionIngress.codec.decode bytes
    | .error .malformed
  let some selection := ApplicationDispatchAdmission.selectCommand ingress
    | .error .malformed
  let expectedCommand := ApplicationDispatchCommand.command ingress.dispatch selection ingress.parent
  let transactionId := DeclaredResourceController.transactionId ingress.dispatch.domain
    ingress.dispatch.semantics expectedCommand
  let some index := verified.opened.durable.firstIndex transactionId
    | .ok none
  let some record := verified.opened.durable.image.accepted[index]?
    | .error .nativeHistoryUnavailable
  let some receipt := verified.receiptAt index
    | .error .nativeHistoryUnavailable
  let expectedEvent := ApplicationDispatchAdmissionIngress.event ingress
  let expectedNullifier := ApplicationDispatchAdmissionIngress.nullifier ingress
  if record.event == expectedEvent &&
      record.nullifiers.contains expectedNullifier &&
      receipt.transactionId == transactionId &&
      receipt.eventId == expectedEvent.eventId &&
      receipt.acceptedCount == index + 1 then
    .ok (some receipt)
  else .error .transactionConflict

/-- The transaction id of the exact call an ingress names (`ApplicationDispatchCommand.command`
of its selected command). -/
def callTransaction (ingress : ApplicationDispatchAdmissionIngress.Ingress) :
    Option Minidregg.Theory.TypedAuthorization.Digest := do
  let selection ← ApplicationDispatchAdmission.selectCommand ingress
  pure (DeclaredResourceController.transactionId ingress.dispatch.domain ingress.dispatch.semantics
    (ApplicationDispatchCommand.command ingress.dispatch selection ingress.parent))

/-- A light lookup's answer under `head`: the call's verified absence, or its original receipt. -/
inductive LightAnswer {store : DurableHistory.StoreIdentity} (head : DurableHistory.Head store)
    (transactionId : Minidregg.Theory.TypedAuthorization.Digest) where
  | absent (opens : DurableIndex.Opens head.indexRoot (DurableIndex.transactionKey transactionId) none)
  | historical (receipt : NativeHostCodec.Receipt)

/-- **Status lookup through the Store's history**: the call's transaction id read by the
Reader; its record answers by its receipt only when it carries exactly this ingress's event and
nullifier (the walk's check), a conflict otherwise. It never re-admits a past request under current
law, nor constructs a physical delivery permit. -/
def lookupLight {store : DurableHistory.StoreIdentity}
    (reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress) (transactionId : Minidregg.Theory.TypedAuthorization.Digest) :
    IO (Except Error (LightAnswer reader.head transactionId)) := do
  match ← reader.byTx transactionId with
  | .error _ => return .error .nativeHistoryUnavailable
  | .ok (.absent opens) => return .ok (.absent opens)
  | .ok (.present found) =>
      let record := found.read.record
      let expectedEvent := ApplicationDispatchAdmissionIngress.event ingress
      if record.event == expectedEvent &&
          record.nullifiers.contains (ApplicationDispatchAdmissionIngress.nullifier ingress) then
        return .ok (.historical (NativeHost.receiptOfFound transactionId found))
      else return .error .transactionConflict

/-- `lookupLight` from request bytes: `none` for a call absent from the history. -/
def lookupLightBytes {store : DurableHistory.StoreIdentity}
    (reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store) (bytes : List UInt8) :
    IO (Except Error (Option NativeHostCodec.Receipt)) := do
  let some ingress := ApplicationDispatchAdmissionIngress.codec.decode bytes
    | return .error .malformed
  let some transactionId := callTransaction ingress
    | return .error .malformed
  match ← lookupLight reader ingress transactionId with
  | .error reason => return .error reason
  | .ok (.absent _) => return .ok none
  | .ok (.historical receipt) => return .ok (some receipt)

end Minidregg.Kernel.ApplicationDispatchLookup
