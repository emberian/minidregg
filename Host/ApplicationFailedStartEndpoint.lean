/- Exact current-law failed-START recovery endpoint. Native custody observes the
OS; this source boundary admits the historical claim, current authenticated law,
signed dead-incarnation evidence and exact durable state transition. -/
module

public import Host.ApplicationFailedStartRecoveryAuthoring
public import Host.ApplicationFailedStartRecoveryTools

@[expose] public section

namespace Minidregg.Host.ApplicationFailedStartEndpoint
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.NativeHost
set_option autoImplicit false

abbrev prepareLight := ApplicationFailedStartRecoveryAuthoring.prepareRequestLight
abbrev assemble := ApplicationFailedStartRecoveryAuthoring.assemble

inductive LightResult where
  | confirmed (kind : DurableReceiverIO.Confirmation) (transactionId : Digest)
      (eventId : Digest)
  | rejected (detail : String)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def submitLight (config : Config) (transport : DurableReceiverIO.Transport)
    (light : NativeHostLight.Light config) (bytes : List UInt8)
    (adopt : NativeHostLight.Adopt light.opening := fun _ _ _ _ => pure ()) : IO LightResult := do
  let some ingress := ApplicationFailedStartRecoveryIngress.codec.decode bytes
    | return .rejected "noncanonical failed-start recovery ingress"
  let grounded ← match ← light.groundedVia transport
      (ApplicationFailedStartRecoveryAdmission.keys config ingress) with
    | .error detail => return .unavailable detail
    | .ok grounded => pure grounded
  let reader := light.opening.reader transport ResourceBirthCodec.rootBytes
  let conditional ← match ← ApplicationFailedStartRecoveryAdmission.prepareConditional config reader
      grounded ingress with
    | .error detail => return .rejected detail
    | .ok conditional => pure conditional
  let intent := ApplicationFailedStartRecoveryCore.intent conditional
  match grounded.ground.recorded intent.transactionId with
  | none => return .rejected "failed-start recovery transaction identity undeclared"
  | some (some _) => return .rejected "failed-start recovery transaction identity already used"
  | some none =>
      match ← DurableServed.receiveServed transport ResourceBirthCodec.rootBytes light.opening intent with
      | .appended kind next _ _ _ _ moved =>
          adopt next _ moved none
          return .confirmed kind intent.transactionId intent.event.eventId
      | .replayed _ => return .rejected "failed-start recovery transaction identity already used"
      | .rejected _ => return .rejected "durable failed-start recovery refused"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

def lookupLight {config : Config} (light : NativeHostLight.Light config)
    (bytes : List UInt8) : IO Outcome := do
  let some ingress := ApplicationFailedStartRecoveryIngress.codec.decode bytes
    | return .refused .malformed "failed-start-recovery".toUTF8.toList
        "noncanonical recovery ingress".toUTF8.toList
  let transactionId := DeclaredResourceController.transactionId ingress.domain
    ingress.semantics (ingress.source.command ingress.domain ingress.semantics)
  let reader := light.opening.reader config.transport ResourceBirthCodec.rootBytes
  match ← reader.byTx transactionId with
  | .error _ =>
      return .uncertain "original failed START recovery receipt unavailable".toUTF8.toList
  | .ok (.absent _) => return .absent
  | .ok (.present found) =>
      let record := found.read.record
      let receipt := NativeHost.receiptOfRecord found.read
      let event := ApplicationFailedStartRecoveryIngress.event ingress
      let reportNullifier := ApplicationFailedStartRecoveryIngress.stableNullifier ingress
      let creationExact := match ingress.creationMarker with
        | none => true
        | some marker => record.nullifiers.contains marker
      if record.event == event && record.nullifiers.contains reportNullifier && creationExact &&
          receipt.transactionId == transactionId &&
          receipt.eventId == event.eventId && receipt.acceptedCount == found.height then
        return .confirmed .replayed receipt
      else
        return .refused .conflict "failed-start-recovery".toUTF8.toList
          "exact recovery ingress/receipt conflict".toUTF8.toList

end Minidregg.Host.ApplicationFailedStartEndpoint
