/- Actual current owner AND renter consent over the same exact source/control
proposal. Each signed invocation is normally admitted (law, credentials,
audience, resources). The ONE derived source phase record retains both
nullifier/guard families and complete actual charges, not synthetic permission.
-/
import Compiler.PortableHomeTransferFrame
import Kernel.DeclaredResourceController
namespace Minidregg.Kernel.PortableHomeTransferAdmission
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.PortableHomeTransfer
open Minidregg.Kernel.PortableContinuationManifest
set_option autoImplicit false

instance (state : State) (plan : Plan) : Decidable (Binds state plan) := by
  unfold Binds; infer_instance

def preparedState (before : State) (plan : Plan) : State :=
  { before with
    epoch := before.epoch + 1, phase := .prepared,plan := some plan,
    cut := none,successorCustody := [],oldFence := [],destinationReceipt := [],
    liabilities := plan.liabilities,activationRequest := []}

structure Prepared {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) where
  private mk ::
  pin : PortableHomeTransferFrame.Pin
  before : State
  plan : Plan
  after : State
  intent : DataIntent ResourceBirthCodec.rootBytes
  ownerSigned : Bytes
  renterSigned : Bytes
  binding : Binds before plan
  beforeExact : PortableHomeTransferFrame.readState pin
    (ground.view.canonicalBytes pin.cell) = some before
  sourceExact : plan.source.point = PortableContinuationManifestCodec.pointOf plan.source.identity durable.image
  sourceControlExact : plan.sourceControlRoot = ground.view.model.roots pin.cell
  afterExact : after = preparedState before plan
  ownerPermission : ∃ (command : Command) (signed : SignedCommand)
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (shape : PhysicalShape prepared) (accepted : AcceptedInvocation prepared signed),
    (accepted.dataIntent shape).subject = some plan.owner.subject ∧
    (accepted.checked none rfl).receipt.prepared.controller.key.publicKey = plan.owner.publicKey ∧
    ownerSigned = signedBytes deployment.domain profile.semantics signed
  renterPermission : ∃ (command : Command) (signed : SignedCommand)
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (shape : PhysicalShape prepared) (accepted : AcceptedInvocation prepared signed),
    (accepted.dataIntent shape).subject = some plan.renter.subject ∧
    (accepted.checked none rfl).receipt.prepared.controller.key.publicKey = plan.renter.publicKey ∧
    renterSigned = signedBytes deployment.domain profile.semantics signed

variable {F : Type} [Field F] [DecidableEq F]
  {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
  {ambient : Ambient} {ground : Ground deployment} {ownerCommand renterCommand : Command}
  {ownerPrepared : PreparedInvocation deployment profile ambient ground ownerCommand}
  {renterPrepared : PreparedInvocation deployment profile ambient ground renterCommand}
  {ownerSigned renterSigned : SignedCommand}

/-- Only preparation is exported until the actual native stage producers are
joined. There is NO raw phase receipt or generic callback-to-activation API.
Both source commands must produce the exact same complete control write. -/
def prepare (pin : PortableHomeTransferFrame.Pin) (plan : Plan)
    (ownerShape : PhysicalShape ownerPrepared) (renterShape : PhysicalShape renterPrepared)
    (owner : AcceptedInvocation ownerPrepared ownerSigned)
    (renter : AcceptedInvocation renterPrepared renterSigned) :
    Option (Prepared deployment profile ambient durable) := do
  match beforeExact : PortableHomeTransferFrame.readState pin (ground.view.canonicalBytes pin.cell) with
  | none => none
  | some before =>
    if !(decide (CanPrepare before)) then none else
    if binding : Binds before plan then
      if sourceExact : plan.source.point = PortableContinuationManifestCodec.pointOf plan.source.identity durable.image then
        if controlExact : plan.sourceControlRoot = ground.view.model.roots pin.cell then
          let ownerIntent := owner.dataIntent ownerShape
          let renterIntent := renter.dataIntent renterShape
          if ownerSubject : ownerIntent.subject = some plan.owner.subject then
            if renterSubject : renterIntent.subject = some plan.renter.subject then
              if ownerKey : (owner.checked none rfl).receipt.prepared.controller.key.publicKey = plan.owner.publicKey then
                if renterKey : (renter.checked none rfl).receipt.prepared.controller.key.publicKey = plan.renter.publicKey then
                  let [write] := ownerIntent.writes | none
                  if write.cellId != pin.cell then none else
                  if renterIntent.writes != ownerIntent.writes then none else
                  let after := preparedState before plan
                  let some actualAfter := PortableHomeTransferFrame.readState pin write.canonicalPostBytes | none
                  if PortableHomeTransferCodec.stateStream.encode actualAfter !=
                      PortableHomeTransferCodec.stateStream.encode after then none else
                  let guards := ownerIntent.readGuards ++ renterIntent.readGuards
                  if readonly : ∀ guard ∈ guards, guard.cellId ∉ ownerIntent.writes.map DataWrite.cellId then
                    let ownerBytes := signedBytes deployment.domain profile.semantics ownerSigned
                    let renterBytes := signedBytes deployment.domain profile.semantics renterSigned
                    let envelope := PortableHomeTransferCodec.encodeEnvelope ⟨plan,ownerBytes,renterBytes⟩
                    let intent : DataIntent ResourceBirthCodec.rootBytes :=
                      { ownerIntent with
                        readGuards := guards,
                        nullifiers := ownerIntent.nullifiers ++ renterIntent.nullifiers,
                        exactCharge := ownerIntent.exactCharge + renterIntent.exactCharge +
                          (fun lane => if lane = .turnBytes then envelope.length else 0),
                        event := {ownerIntent.event with codecVersion := 65,canonicalBytes := envelope},
                        guardsReadOnly := readonly}
                    if !Minidregg.Theory.ResourceCost.Charge.fundedCheck
                        (before.maintenanceReserve + intent.exactCharge) ground.view.model.available then none else
                    if intent.preflight ground.view != .ok () then none else
                    some ⟨pin,before,plan,after,intent,ownerBytes,renterBytes,binding,beforeExact,
                      sourceExact,controlExact,rfl,
                      ⟨ownerCommand,ownerSigned,ownerPrepared,ownerShape,owner,ownerSubject,ownerKey,rfl⟩,
                      ⟨renterCommand,renterSigned,renterPrepared,renterShape,renter,renterSubject,renterKey,rfl⟩⟩
                  else none
                else none
              else none
            else none
          else none
        else none
      else none
    else none

end Minidregg.Kernel.PortableHomeTransferAdmission
