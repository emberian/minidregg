/- First protected Activity phase: actual native governed neutral content birth.
This grants no activity execution or dispatcher permit. Initializing a real
machine is a separate source-admitted event62 operation on the bare cell. -/
import Kernel.NativeHostContext
import Kernel.ResourceBirthReceiver

namespace Minidregg.Kernel.BendActivityBootstrap
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.NativeHost
set_option autoImplicit false

private def eligible {config : Config} {opened : Opened config}
    (pin : ContentControlFrame.Pin)
    (accepted : ResourceBirthPolicyController.Concrete.AcceptedBirth config.profile config.deployment
      opened.pins opened.durable (logicalHeight config opened.durable)) : Bool :=
  match accepted.descriptor.births with
  | [item] =>
    decide (item.owner = pin.owner) && decide (item.create.cellId = pin.cell.value) &&
    decide (item.create.cell.kind = .content) &&
    decide (BendActivityControl.phase pin (opened.durable.snapshot.canonicalBytes pin.cell) = some .absent) &&
    (ResourceBirthReceiver.intent accepted).writes.any (fun write =>
      write.cellId == pin.cell && BendActivityControl.phase pin write.canonicalPostBytes == some .bare)
  | _ => false

structure Admission (config : Config) (opened : Opened config)
    (intent : DataIntent ResourceBirthCodec.rootBytes) where
  private mk ::
  pin : ContentControlFrame.Pin
  pinned : config.activityControl = some pin
  accepted : ResourceBirthPolicyController.Concrete.AcceptedBirth config.profile config.deployment
    opened.pins opened.durable (logicalHeight config opened.durable)
  intentExact : intent = ResourceBirthReceiver.intent accepted
  shape : eligible pin accepted = true

def admit {config : Config} {opened : Opened config}
    (accepted : ResourceBirthPolicyController.Concrete.AcceptedBirth config.profile config.deployment
      opened.pins opened.durable (logicalHeight config opened.durable)) :
    Option (Admission config opened (ResourceBirthReceiver.intent accepted)) := do
  let some pin := config.activityControl | none
  if pinned : config.activityControl = some pin then
    if shape : eligible pin accepted = true then some ⟨pin,pinned,accepted,rfl,shape⟩ else none
  else none

/-- The current admitted birth owns only its Activity facet exception; joint
protection, the real tail law, CAS and exact durable readback are unchanged.
Using config.transport preserves its refusal of unordered local consensus writes. -/
def transport {config : Config} {opened : Opened config}
    {intent : DataIntent ResourceBirthCodec.rootBytes}
    (admitted : Admission config opened intent) : DurableReceiverIO.Transport :=
  { config.transport with sourceGate := fun snapshot proposed => do
      config.otherFacetGate .activity snapshot proposed
      if DurableReceiverCodec.intentStream.encode (DurableReceiver.IntentRecord.ofIntent proposed) =
          DurableReceiverCodec.intentStream.encode (DurableReceiver.IntentRecord.ofIntent intent) ∧
          snapshot.canonicalBytes admitted.pin.cell = opened.durable.snapshot.canonicalBytes admitted.pin.cell
      then .ok () else .error (.durable .transactionConflict) }

theorem transport_other_facets {config : Config} {opened : Opened config}
    {intent : DataIntent ResourceBirthCodec.rootBytes}
    (admitted : Admission config opened intent)
    (snapshot : DataSnapshot ResourceBirthCodec.rootBytes)
    (proposed : DataIntent ResourceBirthCodec.rootBytes)
    (accepted : (transport admitted).sourceGate snapshot proposed = .ok ()) :
    config.otherFacetGate .activity snapshot proposed = .ok () := by
  cases checked : config.otherFacetGate .activity snapshot proposed with
  | error reason => simp [transport, checked] at accepted
  | ok value => cases value; exact checked

#assert_axioms admit
#assert_axioms transport
#assert_axioms transport_other_facets
end Minidregg.Kernel.BendActivityBootstrap
