/- Durable event20 activation under a native-verified Mini prefix. Historical
lookup selects the exact original registration and four-field receipt without
rechecking a changed current gateway law. Fresh work checks the configured
gateway, same-walk frontier/anchor, and one namespace nullifier before CAS.
Neither a conditional plan nor a local fn status is itself Mini acceptance. -/
module

public import Kernel.FnConsumerNamespaceAdmission
public import Kernel.NativeHost

@[expose] public section

namespace Minidregg.Kernel.FnConsumerNamespaceReceiver

open Minidregg.Kernel
open Minidregg.Kernel.FnConsumerNamespaceRegistration
open Minidregg.Compiler

set_option autoImplicit false

/-- `none` means no transaction with this ID; an error means a historical
conflict or an unavailable exact verifier-selected registration. -/
def lookupVerified {config : NativeHost.Config} {target : NativeHost.Durable}
    (verified : NativeHostReplay.Verified config target) (ingress : Ingress) :
    Option (Except String NativeHostCodec.Receipt) := do
  let transaction := transactionId ingress.spec
  let some _ := verified.opened.durable.image.accepted.find?
      (fun record => record.transactionId == transaction)
    | none
  let some receipt := NativeHost.historicalReceipt config verified.opened.durable
      transaction (event ingress).eventId
    | some (.error "fn consumer namespace transaction conflict")
  match verified.frontierRegistration ingress.spec.key receipt with
  | .error _ => some (.error "fn consumer namespace original unavailable")
  | .ok original =>
      if original.ingress == ingress then some (.ok receipt)
      else some (.error "fn consumer namespace original differs")

inductive Result where
  | confirmed (kind : DurableReceiverIO.Confirmation)
      (receipt : NativeHostCodec.Receipt)
  | rejected (reason : String)
  | transactionConflict
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def confirmReadback (config : NativeHost.Config) (ingress : Ingress)
    (kind : DurableReceiverIO.Confirmation) : IO Result := do
  match ← NativeHostLight.start config with
  | .error _ => return .uncertain "fn consumer namespace readback unavailable"
  | .ok light =>
      let tx := transactionId ingress.spec
      let ev := (event ingress).eventId
      match ← (light.opening.reader config.transport ResourceBirthCodec.rootBytes).byTx tx with
      | .error refusal =>
          return .uncertain ("fn consumer namespace readback history reader: " ++ refusal.message)
      | .ok (.absent _) =>
          return .uncertain "fn consumer namespace original receipt unavailable"
      | .ok (.present found) =>
          let record := found.read.record
          let receipt := NativeHost.receiptOfRecord found.read
          if record.event.eventId != ev || receipt.eventId != ev then
            return .uncertain "fn consumer namespace original receipt unavailable"
          let some original := FnConsumerNamespaceHistory.selectAt
              config.deployment.domain config.profile.semantics record receipt
            | return .uncertain "fn consumer namespace original receipt unavailable"
          if original.ingress == ingress &&
              record.nullifiers.contains (claimNullifier ingress.spec) then
            return .confirmed kind receipt
          else
            return .uncertain "fn consumer namespace original receipt unavailable"

def receiveVerified {config : NativeHost.Config} {target : NativeHost.Durable}
    (verified : NativeHostReplay.Verified config target) (bytes : List UInt8) :
    IO Result := do
  let some ingress := ingressCodec.decode bytes
    | return .rejected "noncanonical fn consumer namespace ingress"
  match lookupVerified verified ingress with
  | some (.ok receipt) => return .confirmed .replayed receipt
  | some (.error _) => return .transactionConflict
  | none =>
      match ← FnConsumerNamespaceAdmission.admitVerified verified ingress with
      | .error _ => return .rejected "fn consumer namespace admission refused"
      | .ok accepted =>
          match ← DurableReceiverIO.receiveLoaded config.transport
              ResourceBirthCodec.rootBytes verified.opened.durable
              (accepted.intent verified ingress) with
          | .confirmed kind _ => confirmReadback config ingress kind
          | .rejected _ => return .rejected "fn consumer namespace durable refusal"
          | .contention => return .contention
          | .unavailable detail => return .unavailable detail
          | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.FnConsumerNamespaceReceiver
