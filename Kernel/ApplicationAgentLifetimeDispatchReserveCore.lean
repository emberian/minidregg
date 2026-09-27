/-
The original accepted purse reserve for one exact event26 grant/request. This
component binds a Replay-minted raw ordinary invocation to the distinct v3
context; it does not itself prove membership in the admitted chronology.
-/
import Kernel.ApplicationAgentLifetimeDispatchReserveContext
import Kernel.ApplicationDispatchAgentReserveCore

namespace Minidregg.Kernel.ApplicationAgentLifetimeDispatchReserveCore

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ApplicationAgentLifetimeDispatchReserveContext

set_option autoImplicit false

structure ReservedEvidence (config : Config) where
  private mk ::
  context : Context
  record : DurableReceiver.IntentRecord
  receipt : NativeHostCodec.Receipt
  receiptTransaction : receipt.transactionId = record.transactionId
  receiptEvent : receipt.eventId = record.event.eventId
  beforeState : AgentGrain.State
  beforeRoot : Digest
  capability : CapabilityId
  observe : CapabilityId
  sourceExact :
    ∃ (original : Durable)
      (command : DeclaredResourceController.Command)
      (signed : DeclaredResourceController.SignedCommand)
      (prepared : DeclaredResourceController.PreparedInvocation
        config.deployment config.profile
        ⟨config.federation, logicalHeight config original⟩ original command)
      (shape : DeclaredResourceController.PhysicalShape prepared)
      (accepted : DeclaredResourceController.AcceptedInvocation prepared signed),
      command.subject = context.base.payerSubject ∧
      command.nonce = reserveNonce context ∧
      command.targets = [AgentGrain.Operation.target (.reserve context.base.reserveAmount)
        context.base.purseTask capability beforeRoot beforeState (some observe)] ∧
      beforeState.generation = context.base.purseGeneration ∧
      (beforeState.status = 1 ∨ beforeState.status = 2) ∧
      beforeState.reserved = 0 ∧
      0 ≤ context.base.maximumCharge ∧
      context.base.maximumCharge ≤ context.base.reserveAmount ∧
      context.base.reserveAmount ≤ beforeState.remaining ∧
      record = DurableReceiver.IntentRecord.ofIntent (accepted.dataIntent shape)

/-- The raw evidence is created only by full original ordinary-invocation
admission at Replay. The v3 nonce and target equality are checked against the
same retained command/receipt, never a current purse inferred after the fact. -/
def bindContext {config : Config}
    (raw : ApplicationDispatchAgentReserveCore.RawEvidence config)
    (context : Context) : Except String (ReservedEvidence config) := do
  if subjectExact : raw.command.subject = context.base.payerSubject then
    if nonceExact : raw.command.nonce = reserveNonce context then
      if targetExact : raw.command.targets =
          [AgentGrain.Operation.target (.reserve context.base.reserveAmount)
            context.base.purseTask raw.capability raw.beforeRoot raw.beforeState
            (some raw.observe)] then
        if generationExact : raw.beforeState.generation = context.base.purseGeneration then
          if statusExact : raw.beforeState.status = 1 ∨ raw.beforeState.status = 2 then
            if unreserved : raw.beforeState.reserved = 0 then
              if nonnegative : 0 ≤ context.base.maximumCharge then
                if chargeBound : context.base.maximumCharge ≤ context.base.reserveAmount then
                  if allowance : context.base.reserveAmount ≤ raw.beforeState.remaining then
                    let sourceExact :
                        ∃ (original : Durable)
                          (command : DeclaredResourceController.Command)
                          (signed : DeclaredResourceController.SignedCommand)
                          (prepared : DeclaredResourceController.PreparedInvocation
                            config.deployment config.profile
                            ⟨config.federation, logicalHeight config original⟩
                            original command)
                          (shape : DeclaredResourceController.PhysicalShape prepared)
                          (accepted : DeclaredResourceController.AcceptedInvocation prepared signed),
                          command.subject = context.base.payerSubject ∧
                          command.nonce = reserveNonce context ∧
                          command.targets = [AgentGrain.Operation.target
                            (.reserve context.base.reserveAmount) context.base.purseTask
                            raw.capability raw.beforeRoot raw.beforeState (some raw.observe)] ∧
                          raw.beforeState.generation = context.base.purseGeneration ∧
                          (raw.beforeState.status = 1 ∨ raw.beforeState.status = 2) ∧
                          raw.beforeState.reserved = 0 ∧
                          0 ≤ context.base.maximumCharge ∧
                          context.base.maximumCharge ≤ context.base.reserveAmount ∧
                          context.base.reserveAmount ≤ raw.beforeState.remaining ∧
                          raw.record = DurableReceiver.IntentRecord.ofIntent
                            (accepted.dataIntent shape) := by
                      rcases raw.sourceExact with ⟨original, prepared, shape,
                        accepted, recordExact⟩
                      exact ⟨original, raw.command, raw.signed, prepared, shape,
                        accepted, subjectExact, nonceExact, targetExact,
                        generationExact, statusExact, unreserved, nonnegative,
                        chargeBound, allowance, recordExact⟩
                    return ⟨context, raw.record, raw.receipt,
                      raw.receiptTransaction, raw.receiptEvent,
                      raw.beforeState, raw.beforeRoot, raw.capability, raw.observe,
                      sourceExact⟩
                  else throw "lifetime reserve original allowance insufficient"
                else throw "lifetime reserve charge exceeds original amount"
              else throw "lifetime reserve charge negative"
            else throw "lifetime reserve original purse was held"
          else throw "lifetime reserve original purse was not attached"
        else throw "lifetime reserve original generation differs"
      else throw "lifetime reserve original target differs"
    else throw "lifetime reserve original nonce differs"
  else throw "lifetime reserve original payer subject differs"

/-- This one-use key deliberately reuses event21's *receipt-based* reserve
claim namespace. It prevents the same accepted reserve from being claimed
under both dispatch versions even if a future nonce profile is extended. -/
def claimBytes {config : Config} (reserved : ReservedEvidence config) : List UInt8 :=
  "DREGG/APPLICATION/AGENT-DISPATCH-RESERVE-CLAIM/v2".toUTF8.toList ++
    (StreamCodec.product digestStream digestStream).encode
      (reserved.receipt.transactionId, reserved.receipt.eventId)

def claimNullifier {config : Config} (reserved : ReservedEvidence config) :
    StableNullifier where
  codecVersion := 21
  domain := reserved.context.base.domain
  nullifierId := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/AGENT-DISPATCH-RESERVE-CLAIM-ID/v2".toUTF8.toList
    (claimBytes reserved)).digest
  canonicalBytes := claimBytes reserved

end Minidregg.Kernel.ApplicationAgentLifetimeDispatchReserveCore
