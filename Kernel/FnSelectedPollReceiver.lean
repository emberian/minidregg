/-
Event17 receiving under the exact verified Mini history. A local fn poll is
testimony, not a durable receipt: only exact CAS and verified readback confirm
coverage. Historical lookup returns a receipt and never authorizes an ACK.
-/
import Kernel.FnSelectedPollAdmission
import Kernel.NativeHost

namespace Minidregg.Kernel.FnSelectedPollReceiver

open Minidregg.Kernel
open Minidregg.Kernel.FnSelectedPollCoverage
open Minidregg.Compiler

set_option autoImplicit false

def lookupVerified {config : NativeHost.Config} {target : NativeHost.Durable}
    (verified : NativeHostReplay.Verified config target) (ingress : Ingress) :
    Option (Except String NativeHostCodec.Receipt) := do
  let transaction := transactionId ingress.spec
  let some record := verified.opened.durable.image.accepted.find?
      (fun record => record.transactionId == transaction)
    | none
  let some receipt := NativeHost.historicalReceipt config verified.opened.durable
      transaction (event ingress).eventId
    | some (.error "selected fn poll transaction conflict")
  if record.event == event ingress &&
      record.nullifiers.contains (frontierNullifier ingress.spec) then
    some (.ok receipt)
  else some (.error "selected fn poll original differs")

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
  | .error _ => return .uncertain "selected fn poll readback unavailable"
  | .ok opened =>
      match ← NativeHostReplay.verifyLoaded config opened.durable with
      | .error _ => return .uncertain "selected fn poll readback unverified"
      | .ok verified =>
          match lookupVerified verified ingress with
          | some (.ok receipt) => return .confirmed kind receipt
          | _ => return .uncertain "selected fn poll original receipt unavailable"

def receiveVerified {config : NativeHost.Config} {target : NativeHost.Durable}
    (verified : NativeHostReplay.Verified config target) (bytes : List UInt8) :
    IO Result := do
  let some ingress := ingressCodec.decode bytes
    | return .rejected "noncanonical selected fn poll ingress"
  match lookupVerified verified ingress with
  | some (.ok receipt) => return .confirmed .replayed receipt
  | some (.error _) => return .transactionConflict
  | none =>
      match ← FnSelectedPollAdmission.admitVerified verified ingress with
      | .error _ => return .rejected "selected fn poll admission refused"
      | .ok accepted =>
          match ← DurableReceiverIO.receiveLoaded config.storage.transport
              ResourceBirthCodec.rootBytes verified.opened.durable
              (accepted.intent verified ingress) with
          | .confirmed kind _ => confirmReadback config ingress kind
          | .rejected _ => return .rejected "selected fn poll durable refusal"
          | .contention => return .contention
          | .unavailable detail => return .unavailable detail
          | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.FnSelectedPollReceiver
