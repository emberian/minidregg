/-
Read-only original-receipt lookup for a special dispatch transaction. It
returns status only: a past receipt cannot be converted into a fresh physical
HTTP delivery permit, regardless of whether the request bytes repeat.
-/
import Kernel.NativeHostReplay
import Kernel.ApplicationDispatchAdmission

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
  let some index := verified.opened.durable.image.accepted.findIdx?
      (fun record => record.transactionId == transactionId)
    | .ok none
  let some record := verified.opened.durable.image.accepted[index]?
    | .error .nativeHistoryUnavailable
  let some receipt := verified.receipts[index]?
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

end Minidregg.Kernel.ApplicationDispatchLookup
