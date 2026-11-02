/-
Read-only STOP custody join. A detached op66 plan is presentation, so this
inspector also selects the admitted event23/24 originals and the prior running
event25 from the same current Verified history. The caller must compare the
echoed bytes to its retained op66 plan and fresh op26 callback; this function
does not mint a launch permit or attest systemd itself.
-/
module

public import Host.ApplicationLifecycleLaunchBeginInspection
public import Host.ApplicationLifecycleClaimV3Inspection

@[expose] public section

namespace Minidregg.Host.ApplicationLifecycleStopClaimInspection

open Lean
open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Host.ApplicationLifecycleLaunchBeginAuthoring

set_option autoImplicit false

private def decimal (value : Nat) : Json := .str (toString value)
private def nibble (value : Nat) : Char :=
  "0123456789abcdef".toList[value]?.getD '0'
private def hex (bytes : List UInt8) : Json :=
  .str <| String.ofList <| bytes.flatMap fun byte =>
    [nibble (byte.toNat / 16), nibble (byte.toNat % 16)]
private def receiptJson (receipt : NativeHostCodec.Receipt) : Json := .mkObj
  [("transactionId", decimal receipt.transactionId.value),
   ("eventId", decimal receipt.eventId.value),
   ("acceptedCount", decimal receipt.acceptedCount),
   ("worldRoot", decimal receipt.worldRoot.value)]

private def selectReceiptLight {store : DurableHistory.StoreIdentity}
    (reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store)
    (transactionId : Minidregg.Theory.TypedAuthorization.Digest)
    (event : Minidregg.Kernel.DurableDataIntent.StableEvent)
    (nullifier : Minidregg.Kernel.DurableDataIntent.StableNullifier)
    (missingMessage : String) : IO (Except String NativeHostCodec.Receipt) := do
  match ← reader.byTx transactionId with
  | .error refusal => return .error refusal.message
  | .ok (.absent _) => return .error missingMessage
  | .ok (.present found) =>
      let record := found.read.record
      let receipt := NativeHost.receiptOfRecord found.read
      if record.event == event && record.nullifiers.contains nullifier &&
          receipt.transactionId == transactionId &&
          receipt.eventId == event.eventId && receipt.acceptedCount == found.height then
        return .ok receipt
      else return .error missingMessage

def inspectLight (config : NativeHost.Config) (light : NativeHostLight.Light config)
    (planBytes committedBytes : List UInt8) : IO (Except String Json) := do
  let some plan := stopPlanCodec.decode planBytes
    | return .error "noncanonical STOP running-witness plan"
  unless plan.shape do return .error "STOP running-witness plan shape refused"
  let some committed := ApplicationLifecycleClaimV3Projection.codec.decode committedBytes
    | return .error "noncanonical committed launch claim-v3"
  unless committed.valid do return .error "committed launch claim-v3 shape refused"
  let claim := committed.originalClaim
  let begin := claim.originalBegin
  unless begin.base.source.kind == .stop do
    return .error "committed claim is not STOP"
  let unsigned := plan.base.unsigned
  let expected := { unsigned with base := { unsigned.base with
    signed := begin.base.signed
    packageObservationEnvelope := begin.base.packageObservationEnvelope } }
  unless begin == expected do
    return .error "admitted STOP BEGIN differs from retained operator plan"
  let reader := light.opening.reader config.transport ResourceBirthCodec.rootBytes
  let beginReceipt ← match ← selectReceiptLight reader begin.base.transactionId
      (ApplicationLifecycleBeginV3Ingress.event begin)
      (ApplicationLifecycleBegin.stableNullifier begin.base.domain begin.base.semantics begin.base.source)
      "STOP BEGIN original receipt absent from verified history" with
    | .error detail => return .error detail
    | .ok receipt => pure receipt
  let claimReceipt ← match ← selectReceiptLight reader claim.base.transactionId
      (ApplicationLifecycleClaimV3Ingress.event claim)
      (ApplicationLifecycleClaim.stableNullifier claim.base.domain claim.base.semantics claim.base.source)
      "STOP claim original receipt absent from verified history" with
    | .error detail => return .error detail
    | .ok receipt => pure receipt
  unless claimReceipt == committed.core.claimReceipt do
    return .error "STOP committed claim receipt differs from verified history"
  let selected ← match ← ApplicationLifecycleLaunchBeginAuthoring.selectRunningLight config reader
      light.opening.head.height begin.base.source with
    | .error detail => return .error detail
    | .ok selected => pure selected
  unless selected == plan.running do
    return .error "retained STOP plan differs from verifier-selected running completion"
  let planView ← match ApplicationLifecycleLaunchBeginInspection.inspectStopPlan planBytes with
    | .error detail => return .error detail
    | .ok view => pure view
  let claimView ← match ApplicationLifecycleClaimV3Inspection.inspect committedBytes with
    | .error detail => return .error detail
    | .ok view => pure view
  return .ok (.mkObj [
    ("type", .str "application-lifecycle-stop-claim-verified-v1"),
    ("retainedPlanHex", hex planBytes),
    ("freshCommittedFrameHex", hex committedBytes),
    ("beginReceiptHex", hex (NativeHostCodec.receiptStream.encode beginReceipt)),
    ("beginReceipt", receiptJson beginReceipt),
    ("claimReceiptHex", hex (NativeHostCodec.receiptStream.encode claimReceipt)),
    ("claimReceipt", receiptJson claimReceipt),
    ("runningIndex", decimal selected.index),
    ("runningReceiptHex", hex (NativeHostCodec.receiptStream.encode selected.receipt)),
    ("plan", planView),
    ("claim", claimView)])

end Minidregg.Host.ApplicationLifecycleStopClaimInspection
