/-
Receipt-only lookup for grain-backed share issue event 22. Cold callers
re-admit a selected original prefix; persistent callers consume the compact
issue certificate and receipt from the same native verifier walk. Both require
exact source bytes and full IntentRecord equality, never event-shaped journal
bytes alone.
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

/-- A persistent lookup consumes only the private issue certificate minted by
this exact verified walk. That certificate already retains original native
admission and complete IntentRecord equality; exact ingress bytes preserve the
original-prefix lookup contract without repeating genesis re-admission. The
same-walk receipt remains the original receipt after later appends. -/
def lookupVerified {config : Config} {target : Durable}
    (verified : NativeHostReplay.Verified config target) (bytes : List UInt8) :
    Except Error (Option NativeHostCodec.Receipt) := do
  let some ingress := ApplicationShareIssueGrainSource.codec.decode bytes
    | .error .malformed
  let some grain := ingress.decodeGrain
    | .error .malformed
  let transactionId := grain.source.birth.transactionId
  let some index := verified.opened.durable.image.accepted.findIdx?
      (fun record => record.transactionId == transactionId)
    | .ok none
  let some record := verified.opened.durable.image.accepted[index]?
    | .error .nativeHistoryUnavailable
  let some receipt := verified.receipts[index]?
    | .error .nativeHistoryUnavailable
  let some issue := verified.issues.find? (fun issue => issue.index == index)
    | .error .transactionConflict
  if issue.evidence.ingressBytes == bytes &&
      DurableReceiverCodec.intentStream.encode record ==
        DurableReceiverCodec.intentStream.encode issue.evidence.record &&
      record.event.codecVersion == 22 &&
      receipt == issue.receipt &&
      receipt.transactionId == transactionId &&
      receipt.eventId == record.event.eventId &&
      receipt.acceptedCount == index + 1 then
    .ok (some receipt)
  else .error .transactionConflict

/-- One-shot callers retain original selected-prefix re-admission. The
persistent Host calls `lookupVerified` on its refreshed walked session. -/
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
  let ⟨_, reader⟩ ← match ← DurableHistoryStore.readerOf config.transport ResourceBirthCodec.rootBytes target with
    | .error _ => return .error .nativeHistoryUnavailable
    | .ok reader => pure reader
  let .ok selection ← NativeHostReplay.verifyLoadedSelected config reader target index
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
