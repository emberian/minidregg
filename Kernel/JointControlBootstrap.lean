/- Exact governed source-control initialization. Two source records, not a
cross-record atomicity claim: absent → canonical empty native content → initialized.
No unrelated ordinary operation receives an exception before initialization.
-/
import Kernel.NativeHostContext
import Kernel.ResourceBirthReceiver
import Kernel.DeclaredResourceController
namespace Minidregg.Kernel.JointControlBootstrap
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.DeclaredResourceController
set_option autoImplicit false

inductive Phase | absent | bare | initialized deriving DecidableEq, BEq

def phase (pin : JointControlFrame.Pin) (bytes : List UInt8) : Option Phase := do
  let image ← (ResourceBirthCodec.LifecycleImage.codec CanonicalCellRegistry.registry).decode bytes
  match image with
  | .fresh => some .absent
  | .retired => none
  | .live packed => match packed with
    | ⟨.content,content⟩ =>
      if (JointControlFrame.readControl pin bytes).isSome then some .initialized
      else if CanonicalCellRegistry.UserShape .content content.logical then some .bare else none
    | _ => none

def emptyControl : JointControlCell.Control := ⟨[],[],[],0⟩
def initializer (pin : JointControlFrame.Pin) : ContentResource.Command :=
  ⟨[.createAtom pin.atom (.inlineObject pin.schema) (JointControlCell.controlStream.encode emptyControl)]⟩

private def birthCheck {config : Config} {opened : Opened config}
    (pin : JointControlFrame.Pin)
    (accepted : ResourceBirthPolicyController.Concrete.AcceptedBirth config.profile config.deployment
      opened.pins opened.durable (logicalHeight config opened.durable)) : Bool :=
  match accepted.descriptor.births with
  | [item] =>
      decide (item.owner = pin.owner) && decide (item.create.cellId = pin.cell.value) &&
      decide (item.create.cell.kind = .content) &&
      decide (phase pin (opened.durable.snapshot.canonicalBytes pin.cell) = some .absent) &&
      (ResourceBirthReceiver.intent accepted).writes.any (fun write =>
        write.cellId == pin.cell && phase pin write.canonicalPostBytes == some .bare)
  | _ => false

private def initializeCheck {config : Config} {opened : Opened config} {command : Command}
    {signed : SignedCommand}
    (pin : JointControlFrame.Pin)
    {prepared : PreparedInvocation config.deployment config.profile
      ⟨config.federation,logicalHeight config opened.durable⟩ opened.durable command}
    (shape : PhysicalShape prepared) (accepted : AcceptedInvocation prepared signed) : Bool :=
  match command.targets, (accepted.dataIntent shape).writes with
  | [target], [write] =>
      decide (command.subject = pin.owner) && command.run.isNone &&
      decide (target.kind = .object) && decide (target.target = pin.cell.value) &&
      decide (target.payload = .content (initializer pin)) &&
      decide (write.cellId = pin.cell) &&
      decide (phase pin (opened.durable.snapshot.canonicalBytes pin.cell) = some .bare) &&
      (match JointControlFrame.readControl pin write.canonicalPostBytes with
       | none => false
       | some control => JointControlCell.controlStream.encode control ==
           JointControlCell.controlStream.encode emptyControl)
  | _, _ => false

/-- These private tokens retain actual CURRENT native permission and the exact
phase-specific source operation. Raw accepted-record bytes cannot mint them. -/
inductive CurrentPermission (config : Config) (opened : Opened config) :
    DataIntent ResourceBirthCodec.rootBytes → Type
  | birth (accepted : ResourceBirthPolicyController.Concrete.AcceptedBirth config.profile config.deployment
      opened.pins opened.durable (logicalHeight config opened.durable)) :
      CurrentPermission config opened (ResourceBirthReceiver.intent accepted)
  | initialize {command : Command} {signed : SignedCommand}
      {prepared : PreparedInvocation config.deployment config.profile
        ⟨config.federation,logicalHeight config opened.durable⟩ opened.durable command}
      (shape : PhysicalShape prepared) (accepted : AcceptedInvocation prepared signed) :
      CurrentPermission config opened (accepted.dataIntent shape)

private def CurrentPermission.eligible {config : Config} {opened : Opened config}
    {intent : DataIntent ResourceBirthCodec.rootBytes} (pin : JointControlFrame.Pin) :
    CurrentPermission config opened intent → Bool
  | .birth accepted => birthCheck pin accepted
  | .initialize shape accepted => initializeCheck pin shape accepted

structure Admission (config : Config) (opened : Opened config)
    (intent : DataIntent ResourceBirthCodec.rootBytes) where
  private mk ::
  pin : JointControlFrame.Pin
  pinned : config.jointControl = some pin
  current : CurrentPermission config opened intent
  eligible : CurrentPermission.eligible pin current = true

def admitBirth {config : Config} {opened : Opened config}
    (accepted : ResourceBirthPolicyController.Concrete.AcceptedBirth config.profile config.deployment
      opened.pins opened.durable (logicalHeight config opened.durable)) :
    Option (Admission config opened (ResourceBirthReceiver.intent accepted)) := do
  let some pin := config.jointControl | none
  if pinned : config.jointControl = some pin then
    if eligible : birthCheck pin accepted = true then some ⟨pin,pinned,.birth accepted,eligible⟩ else none
  else none

def admitInitialize {config : Config} {opened : Opened config} {command : Command} {signed : SignedCommand}
    {prepared : PreparedInvocation config.deployment config.profile
      ⟨config.federation,logicalHeight config opened.durable⟩ opened.durable command}
    (shape : PhysicalShape prepared) (accepted : AcceptedInvocation prepared signed) :
    Option (Admission config opened (accepted.dataIntent shape)) := do
  let some pin := config.jointControl | none
  if pinned : config.jointControl = some pin then
    if eligible : initializeCheck pin shape accepted = true then
      some ⟨pin,pinned,.initialize shape accepted,eligible⟩ else none
  else none

/-- A typed initialization exception selects ONE complete current admitted
record. It retains the physical CAS/readback, budget preflight and tail law.
No generic content insert, raw post or client-selected gate is accepted. -/
def transport {config : Config} {opened : Opened config} {intent : DataIntent ResourceBirthCodec.rootBytes}
    (_admitted : Admission config opened intent) : DurableReceiverIO.Transport :=
  { config.physicalTransport with sourceGate := fun snapshot proposed =>
      if DurableReceiverCodec.intentStream.encode (DurableReceiver.IntentRecord.ofIntent proposed) =
          DurableReceiverCodec.intentStream.encode (DurableReceiver.IntentRecord.ofIntent intent) ∧
          (match config.jointControl with
           | none => false
           | some pin => snapshot.canonicalBytes pin.cell == opened.durable.snapshot.canonicalBytes pin.cell) then
        .ok () else .error (.durable .transactionConflict) }
end Minidregg.Kernel.JointControlBootstrap
