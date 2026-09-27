/- Durable event20 activation under a native-verified Mini prefix. Historical
lookup selects the exact original registration and four-field receipt without
rechecking a changed current gateway law. Fresh work checks the configured
gateway, same-walk frontier/anchor, and one namespace nullifier before CAS.
Neither a conditional plan nor a local fn status is itself Mini acceptance. -/
import Kernel.FnConsumerNamespaceAdmission
import Kernel.NativeHost

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
  match ← NativeHost.openExisting config with
  | .error _ => return .uncertain "fn consumer namespace readback unavailable"
  | .ok opened =>
      match ← NativeHostReplay.verifyLoaded config opened.durable with
      | .error _ => return .uncertain "fn consumer namespace readback unverified"
      | .ok verified =>
          match lookupVerified verified ingress with
          | some (.ok receipt) => return .confirmed kind receipt
          | _ => return .uncertain "fn consumer namespace original receipt unavailable"

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
          match ← DurableReceiverIO.receiveLoaded config.storage.transport
              ResourceBirthCodec.rootBytes verified.opened.durable
              (accepted.intent verified ingress) with
          | .confirmed kind _ => confirmReadback config ingress kind
          | .rejected _ => return .rejected "fn consumer namespace durable refusal"
          | .contention => return .contention
          | .unavailable detail => return .unavailable detail
          | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.FnConsumerNamespaceReceiver
