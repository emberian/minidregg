/-
Cycle-safe original reserve evidence for event21. An accepted ordinary
AgentGrain reserve and complete record equality are necessary, but this type
alone does not certify membership in the current admitted history. Replay
must add it only after the exact step advances and validates.
-/
import Kernel.ApplicationDispatchAgentPayer

namespace Minidregg.Kernel.ApplicationDispatchAgentReserveCore

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ApplicationDispatchAgentReserveContext

set_option autoImplicit false

/-- Compact admitted ordinary invocation before its later event21 context is
known. Replay creates this only after full original record/receipt matching,
advance and successor validation. No old physical prefix is retained in data:
the large native Accepted and original durable live in erased proof. -/
structure RawEvidence (config : Config) where
  private mk ::
  record : DurableReceiver.IntentRecord
  receipt : NativeHostCodec.Receipt
  command : DeclaredResourceController.Command
  signed : DeclaredResourceController.SignedCommand
  beforeState : AgentGrain.State
  beforeRoot : Digest
  capability : CapabilityId
  observe : CapabilityId
  receiptTransaction : receipt.transactionId = record.transactionId
  receiptEvent : receipt.eventId = record.event.eventId
  sourceExact :
    ∃ (original : Durable)
      (prepared : DeclaredResourceController.PreparedInvocation config.deployment config.profile
        ⟨config.federation, logicalHeight config original⟩ original command)
      (shape : DeclaredResourceController.PhysicalShape prepared)
      (accepted : DeclaredResourceController.AcceptedInvocation prepared signed),
      record = DurableReceiver.IntentRecord.ofIntent (accepted.dataIntent shape)

def RawEvidence.fromAccepted (config : Config) (original : Durable)
    (command : DeclaredResourceController.Command)
    (signed : DeclaredResourceController.SignedCommand)
    (prepared : DeclaredResourceController.PreparedInvocation config.deployment config.profile
      ⟨config.federation, logicalHeight config original⟩ original command)
    (shape : DeclaredResourceController.PhysicalShape prepared)
    (accepted : DeclaredResourceController.AcceptedInvocation prepared signed)
    (record : DurableReceiver.IntentRecord) (receipt : NativeHostCodec.Receipt)
    (beforeState : AgentGrain.State) (beforeRoot : Digest)
    (capability observe : CapabilityId)
    (recordExact : record = DurableReceiver.IntentRecord.ofIntent
      (accepted.dataIntent shape))
    (receiptTransaction : receipt.transactionId = record.transactionId)
    (receiptEvent : receipt.eventId = record.event.eventId) : RawEvidence config :=
  ⟨record, receipt, command, signed, beforeState, beforeRoot, capability,
    observe, receiptTransaction, receiptEvent,
    ⟨original, prepared, shape, accepted, recordExact⟩⟩

/-- Large original admission is proof-erased; runtime replay retains only the
exact context and record. The private constructor prevents a current reserved
page or caller-supplied receipt from becoming this evidence. -/
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
      (prepared : DeclaredResourceController.PreparedInvocation config.deployment config.profile
        ⟨config.federation, logicalHeight config original⟩ original command)
      (shape : DeclaredResourceController.PhysicalShape prepared)
      (accepted : DeclaredResourceController.AcceptedInvocation prepared signed),
      command.subject = context.payerSubject ∧
      command.nonce = ApplicationDispatchAgentReserveContext.nonce context ∧
      command.targets = [AgentGrain.Operation.target (.reserve context.reserveAmount)
        context.purseTask capability beforeRoot beforeState (some observe)] ∧
      beforeState.generation = context.purseGeneration ∧
      (beforeState.status = 1 ∨ beforeState.status = 2) ∧
      beforeState.reserved = 0 ∧
      0 ≤ context.maximumCharge ∧
      context.maximumCharge ≤ context.reserveAmount ∧
      context.reserveAmount ≤ beforeState.remaining ∧
      record = DurableReceiver.IntentRecord.ofIntent (accepted.dataIntent shape)

def ReservedEvidence.fromAccepted (config : Config) (original : Durable)
    (context : Context) (beforeState : AgentGrain.State) (beforeRoot : Digest)
    (capability observe : CapabilityId)
    (command : DeclaredResourceController.Command)
    (signed : DeclaredResourceController.SignedCommand)
    (prepared : DeclaredResourceController.PreparedInvocation config.deployment config.profile
      ⟨config.federation, logicalHeight config original⟩ original command)
    (shape : DeclaredResourceController.PhysicalShape prepared)
    (accepted : DeclaredResourceController.AcceptedInvocation prepared signed)
    (record : DurableReceiver.IntentRecord)
    (receipt : NativeHostCodec.Receipt)
    (receiptTransaction : receipt.transactionId = record.transactionId)
    (receiptEvent : receipt.eventId = record.event.eventId)
    (subjectExact : command.subject = context.payerSubject)
    (nonceExact : command.nonce = ApplicationDispatchAgentReserveContext.nonce context)
    (targetExact : command.targets = [AgentGrain.Operation.target (.reserve context.reserveAmount)
      context.purseTask capability beforeRoot beforeState (some observe)])
    (generationExact : beforeState.generation = context.purseGeneration)
    (statusExact : beforeState.status = 1 ∨ beforeState.status = 2)
    (unreserved : beforeState.reserved = 0)
    (nonnegative : 0 ≤ context.maximumCharge)
    (chargeBound : context.maximumCharge ≤ context.reserveAmount)
    (allowance : context.reserveAmount ≤ beforeState.remaining)
    (recordExact : record = DurableReceiver.IntentRecord.ofIntent
      (accepted.dataIntent shape)) : ReservedEvidence config :=
  ⟨context, record, receipt, receiptTransaction, receiptEvent,
    beforeState, beforeRoot, capability, observe,
    ⟨original, command, signed, prepared, shape, accepted, subjectExact,
      nonceExact, targetExact, generationExact, statusExact, unreserved,
      nonnegative, chargeBound, allowance, recordExact⟩⟩

/-- Bind a later canonical v2 context to the actual earlier signed command.
The before state/root and selected receipt were retained by Replay, not read
from the event21 ingress. Chronological membership is still Replay's separate
obligation. -/
def RawEvidence.bindContext {config : Config} (raw : RawEvidence config)
    (context : Context) : Except String (ReservedEvidence config) := do
  if subjectExact : raw.command.subject = context.payerSubject then
    if nonceExact : raw.command.nonce =
        ApplicationDispatchAgentReserveContext.nonce context then
      if targetExact : raw.command.targets =
          [AgentGrain.Operation.target (.reserve context.reserveAmount)
            context.purseTask raw.capability raw.beforeRoot raw.beforeState
            (some raw.observe)] then
        if generationExact : raw.beforeState.generation = context.purseGeneration then
          if statusExact : raw.beforeState.status = 1 ∨ raw.beforeState.status = 2 then
            if unreserved : raw.beforeState.reserved = 0 then
              if nonnegative : 0 ≤ context.maximumCharge then
                if chargeBound : context.maximumCharge ≤ context.reserveAmount then
                  if allowance : context.reserveAmount ≤ raw.beforeState.remaining then
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
                          command.subject = context.payerSubject ∧
                          command.nonce = ApplicationDispatchAgentReserveContext.nonce context ∧
                          command.targets = [AgentGrain.Operation.target
                            (.reserve context.reserveAmount) context.purseTask
                            raw.capability raw.beforeRoot raw.beforeState (some raw.observe)] ∧
                          raw.beforeState.generation = context.purseGeneration ∧
                          (raw.beforeState.status = 1 ∨ raw.beforeState.status = 2) ∧
                          raw.beforeState.reserved = 0 ∧
                          0 ≤ context.maximumCharge ∧
                          context.maximumCharge ≤ context.reserveAmount ∧
                          context.reserveAmount ≤ raw.beforeState.remaining ∧
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
                  else throw "dispatch reserve original allowance insufficient"
                else throw "dispatch reserve charge exceeds original amount"
              else throw "dispatch reserve charge negative"
            else throw "dispatch reserve original purse was held"
          else throw "dispatch reserve original purse was not attached"
        else throw "dispatch reserve original generation differs"
      else throw "dispatch reserve original target differs"
    else throw "dispatch reserve original nonce differs"
  else throw "dispatch reserve original payer subject differs"

/-- This key is for one accepted reserve receipt, not a per-HTTP app key.
The canonical context is fixed by the admitted nonce; the original tx/event
pair ensures that a different app transaction cannot claim the same hold. -/
def claimBytes {config : Config} (reserved : ReservedEvidence config) : List UInt8 :=
  "DREGG/APPLICATION/AGENT-DISPATCH-RESERVE-CLAIM/v2".toUTF8.toList ++
    (StreamCodec.product digestStream digestStream).encode
      (reserved.receipt.transactionId, reserved.receipt.eventId)

def claimNullifier {config : Config} (reserved : ReservedEvidence config) :
    StableNullifier where
  codecVersion := 21
  domain := reserved.context.domain
  nullifierId := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/AGENT-DISPATCH-RESERVE-CLAIM-ID/v2".toUTF8.toList
    (claimBytes reserved)).digest
  canonicalBytes := claimBytes reserved

end Minidregg.Kernel.ApplicationDispatchAgentReserveCore
