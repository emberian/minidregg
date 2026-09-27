/-
Read-only STOP custody join. A detached op66 plan is presentation, so this
inspector also selects the admitted event23/24 originals and the prior running
event25 from the same current Verified history. The caller must compare the
echoed bytes to its retained op66 plan and fresh op26 callback; this function
does not mint a launch permit or attest systemd itself.
-/
import Host.ApplicationLifecycleLaunchBeginInspection
import Host.ApplicationLifecycleClaimV3Inspection
import Kernel.ApplicationLifecycleV3Lookup

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

def inspectVerified {config : NativeHost.Config} {target : NativeHost.Durable}
    (verified : NativeHostReplay.Verified config target)
    (planBytes committedBytes : List UInt8) : Except String Json := do
  let some plan := stopPlanCodec.decode planBytes
    | throw "noncanonical STOP running-witness plan"
  unless plan.shape do throw "STOP running-witness plan shape refused"
  let some committed := ApplicationLifecycleClaimV3Projection.codec.decode committedBytes
    | throw "noncanonical committed launch claim-v3"
  unless committed.valid do throw "committed launch claim-v3 shape refused"
  let claim := committed.originalClaim
  let begin := claim.originalBegin
  unless begin.base.source.kind == .stop do
    throw "committed claim is not STOP"
  let unsigned := plan.base.unsigned
  let expected := { unsigned with base := { unsigned.base with
    signed := begin.base.signed
    packageObservationEnvelope := begin.base.packageObservationEnvelope } }
  unless begin == expected do
    throw "admitted STOP BEGIN differs from retained operator plan"
  let beginReceipt ← match ApplicationLifecycleV3Lookup.beginVerified
      verified begin.canonicalBytes with
    | .ok (some receipt) => pure receipt
    | _ => throw "STOP BEGIN original receipt absent from verified history"
  let claimReceipt ← match ApplicationLifecycleV3Lookup.claimVerified
      verified claim.canonicalBytes with
    | .ok (some receipt) => pure receipt
    | _ => throw "STOP claim original receipt absent from verified history"
  unless claimReceipt == committed.core.claimReceipt do
    throw "STOP committed claim receipt differs from verified history"
  let running ← verified.selectRunning begin.base.source
  let prior := running.prior
  let physical := prior.ingress.source.physical.report
  let some custody := physical.volumeCustody
    | throw "admitted running completion lacks volume custody"
  let selected : RunningWitness :=
    { index := prior.index
      receipt := prior.receipt
      generation := prior.ingress.source.originalBegin.base.source.processGeneration
      unit := physical.unit
      image := physical.materializedImage
      invocationId := physical.invocationId
      controlGroup := physical.controlGroup
      custody := custody }
  unless selected == plan.running do
    throw "retained STOP plan differs from verifier-selected running completion"
  let planView ← ApplicationLifecycleLaunchBeginInspection.inspectStopPlan planBytes
  let claimView ← ApplicationLifecycleClaimV3Inspection.inspect committedBytes
  return .mkObj [
    ("type", .str "application-lifecycle-stop-claim-verified-v1"),
    ("retainedPlanHex", hex planBytes),
    ("freshCommittedFrameHex", hex committedBytes),
    ("beginReceiptHex", hex (NativeHostCodec.receiptStream.encode beginReceipt)),
    ("claimReceiptHex", hex (NativeHostCodec.receiptStream.encode claimReceipt)),
    ("runningIndex", decimal selected.index),
    ("runningReceiptHex", hex (NativeHostCodec.receiptStream.encode selected.receipt)),
    ("plan", planView),
    ("claim", claimView)]

end Minidregg.Host.ApplicationLifecycleStopClaimInspection
