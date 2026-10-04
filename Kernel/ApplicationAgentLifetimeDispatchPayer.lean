/-
The current signed purse witness for a grant-bound event26 reserve. Its v3
nonce commits the immutable grant identity; the old event21 payer witness
and signature domain remain untouched.
-/
import Kernel.ApplicationAgentLifetimeDispatchReserveCore
import Kernel.ApplicationDispatchAgentPayer

namespace Minidregg.Kernel.ApplicationAgentLifetimeDispatchPayer

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.ApplicationAgentLifetimeDispatchReserveContext

set_option autoImplicit false

structure Checked (config : Config) (opened : Opened config)
    (context : Context) where
  private mk ::
  signed : DeclaredResourceController.SignedCommand
  command : DeclaredResourceController.Command
  cell : PackedCell CanonicalCellRegistry.registry
  state : AgentGrain.State
  stateExact : ApplicationDispatchAgentPayer.stateAt context.base.purseTask cell = some state
  payerCapability : CapabilityId
  payerObserve : CapabilityId
  prepared : DeclaredResourceController.PreparedInvocation config.deployment config.profile
    ⟨config.federation, logicalHeight config opened.durable⟩ opened.durable command
  shape : DeclaredResourceController.PhysicalShape prepared
  accepted : DeclaredResourceController.AcceptedInvocation prepared signed
  commandExact : command =
    { subject := context.base.payerSubject
      nonce := payerNonce context
      targets := [AgentGrain.Operation.target .input context.base.purseTask
        payerCapability cell.payload.root state (some payerObserve)] }
  stateGeneration : state.generation = context.base.purseGeneration
  stateReserved : state.status = 3 ∨ state.status = 4
  stateAmount : state.reserved = context.base.reserveAmount
  amountValid : 0 ≤ context.base.maximumCharge ∧
    context.base.maximumCharge ≤ context.base.reserveAmount
  physicalCurrent : ResourceBirthCodec.physicalRoot (.live cell) =
    opened.durable.snapshot.model.roots ⟨context.base.purseTask⟩

def checkCurrent (config : Config) (opened : Opened config)
    (context : Context) (payerCapability payerObserve : CapabilityId)
    (signed : DeclaredResourceController.SignedCommand) :
    IO (Except String (Checked config opened context)) := do
  if context.base.domain != config.deployment.domain ||
      context.base.semantics != config.profile.semantics then
    return .error "lifetime payer domain/profile mismatch"
  let some command := DeclaredResourceController.commandCodec.decode signed.commandBytes
    | return .error "lifetime payer command malformed"
  let some cell := (match opened.directory.directory.slots context.base.purseTask with
    | .present cell => some cell
    | _ => none)
    | return .error "lifetime payer purse unavailable"
  let some state := ApplicationDispatchAgentPayer.stateAt context.base.purseTask cell
    | return .error "lifetime payer purse state unavailable"
  if stateGeneration : state.generation = context.base.purseGeneration then
    if stateReserved : state.status = 3 ∨ state.status = 4 then
      if stateAmount : state.reserved = context.base.reserveAmount then
        if amountValid : 0 ≤ context.base.maximumCharge ∧
            context.base.maximumCharge ≤ context.base.reserveAmount then
          if commandExact : command =
              { subject := context.base.payerSubject
                nonce := payerNonce context
                targets := [AgentGrain.Operation.target .input context.base.purseTask
                  payerCapability cell.payload.root state (some payerObserve)] } then
            match ← DeclaredResourceController.prepareAuthenticated config.deployment config.profile
                ⟨config.federation, logicalHeight config opened.durable⟩ config.signature
                opened.durable command signed.authorityEnvelope with
            | .error _ => return .error "lifetime payer preparation refused"
            | .ok prepared =>
              if shape : DeclaredResourceController.PhysicalShape prepared then
                match ← DeclaredResourceController.admit config.signature prepared signed with
                | .error _ => return .error "lifetime payer native admission refused"
                | .ok accepted =>
                  if stateExact : ApplicationDispatchAgentPayer.stateAt context.base.purseTask
                      cell = some state then
                    if physicalCurrent : ResourceBirthCodec.physicalRoot (.live cell) =
                        opened.durable.snapshot.model.roots ⟨context.base.purseTask⟩ then
                      return .ok ⟨signed, command, cell, state, stateExact,
                        payerCapability, payerObserve, prepared, shape, accepted,
                        commandExact, stateGeneration, stateReserved, stateAmount,
                        amountValid, physicalCurrent⟩
                    else return .error "lifetime payer physical root differs"
                  else return .error "lifetime payer state changed during inspection"
              else return .error "lifetime payer physical shape refused"
          else return .error "lifetime payer target/context mismatch"
        else return .error "lifetime payer charge exceeds hold"
      else return .error "lifetime payer held amount changed"
    else return .error "lifetime payer no longer reserved"
  else return .error "lifetime payer generation changed"

end Minidregg.Kernel.ApplicationAgentLifetimeDispatchPayer
