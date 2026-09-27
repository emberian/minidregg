/-
Receipt-only lookup for grain-backed share issue event 22. The selected
checkpoint comes from the same native verifier walk that admits the current
tip. Re-admission at that original prefix and full IntentRecord equality keep
this lookup from treating event-shaped journal bytes as issuance authority.
-/
import Kernel.ApplicationShareIssueGrainReceiver
import Kernel.NativeHostReplay

namespace Minidregg.Kernel.ApplicationShareIssueGrainLookup

open Minidregg.Compiler
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

inductive Error where
  | malformed
  | transactionConflict
  | nativeHistoryUnavailable
  deriving DecidableEq, Repr

def lookupOriginal (config : Config) (target : Durable) (bytes : List UInt8) :
    IO (Except Error (Option NativeHostCodec.Receipt)) := do
  let some ingress := ApplicationShareIssueGrainSource.codec.decode bytes
    | return .error .malformed
  let some grain := ingress.decodeGrain
    | return .error .malformed
  let transactionId := grain.source.birth.transactionId
  let some index := target.image.accepted.findIdx?
      (fun record => record.transactionId == transactionId)
    | return .ok none
  let .ok selection ← NativeHostReplay.verifyLoadedSelected config target index
    | return .error .nativeHistoryUnavailable
  let before := selection.selected.before
  let ambient : DeclaredResourceController.Ambient :=
    ⟨config.federation, NativeHost.logicalHeight config before.durable⟩
  let .ok ⟨admittedIngress, accepted⟩ ←
      ApplicationShareIssueGrainAdmission.admitNative config.profile config
        before.pins config.signature before.durable ambient bytes
    | return .error .transactionConflict
  let intent := ApplicationShareIssueGrainReceiver.intent accepted
  let receipt := selection.selected.receipt
  if admittedIngress.canonicalBytes == bytes &&
      NativeHostReplay.recordMatches selection.selected.record intent &&
      receipt.transactionId == transactionId &&
      receipt.eventId == intent.event.eventId &&
      receipt.acceptedCount == index + 1 then
    return .ok (some receipt)
  else return .error .transactionConflict

end Minidregg.Kernel.ApplicationShareIssueGrainLookup
