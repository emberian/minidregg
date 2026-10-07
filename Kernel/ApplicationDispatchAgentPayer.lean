/-
Current native admission of a separately delegated dispatch payer. This is
only a component of event21: it does not prove original reserve provenance,
issue provenance, or durable pending commit. The signed no-op is checked at
the same image as the application dispatch; event21 carries its complete-cell
physical root as a read guard rather than writing an unchanged purse page.
-/
import Kernel.ApplicationDispatchAgentReserveContext
import Kernel.NativeHostContext
import Kernel.NativeHostServed

namespace Minidregg.Kernel.ApplicationDispatchAgentPayer

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.IntStream (intStream)
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.ApplicationDispatchAgentReserveContext

set_option autoImplicit false

def payerNonce (context : Context) : Nat :=
  AgentGrain.contextNonce
    ("DREGG/APPLICATION/AGENT-DISPATCH-PAYER/v2".toUTF8.toList ++
      context.canonicalBytes)

def stateAt (task : Nat) (cell : PackedCell CanonicalCellRegistry.registry) :
    Option AgentGrain.State := do
  let ⟨.declaredObject, payload⟩ := cell
    | none
  let page := payload.logical
  AgentGrain.readState task page

structure Checked (config : Config) (opened : Opened config)
    (context : Context) where
  private mk ::
  signed : DeclaredResourceController.SignedCommand
  command : DeclaredResourceController.Command
  cell : PackedCell CanonicalCellRegistry.registry
  state : AgentGrain.State
  stateExact : stateAt context.purseTask cell = some state
  payerCapability : CapabilityId
  payerObserve : CapabilityId
  prepared : DeclaredResourceController.PreparedInvocation config.deployment config.profile
    ⟨config.federation, logicalHeight config opened.durable⟩ opened.ground command
  shape : DeclaredResourceController.PhysicalShape prepared
  accepted : DeclaredResourceController.AcceptedInvocation prepared signed
  commandExact : command =
    { subject := context.payerSubject
      nonce := payerNonce context
      targets := [AgentGrain.Operation.target .input context.purseTask
        payerCapability cell.payload.root state (some payerObserve)] }
  stateGeneration : state.generation = context.purseGeneration
  stateReserved : state.status = 3 ∨ state.status = 4
  stateAmount : state.reserved = context.reserveAmount
  amountValid : 0 ≤ context.maximumCharge ∧
    context.maximumCharge ≤ context.reserveAmount
  physicalCurrent : ResourceBirthCodec.physicalRoot (.live cell) =
    opened.durable.snapshot.model.roots ⟨context.purseTask⟩

/-- Native admission checks the payer's current signature, capability, law,
and exact held purse page at the same image used for app dispatch. A caller's
`payerCapability` and `payerObserve` are selectors only. -/
def checkCurrent (config : Config) (opened : Opened config)
    (context : Context) (payerCapability payerObserve : CapabilityId)
    (signed : DeclaredResourceController.SignedCommand) :
    IO (Except String (Checked config opened context)) := do
  if context.domain != config.deployment.domain ||
      context.semantics != config.profile.semantics then
    return .error "dispatch payer domain/profile mismatch"
  let some command := DeclaredResourceController.commandCodec.decode signed.commandBytes
    | return .error "dispatch payer command malformed"
  let some cell := (match opened.directory.directory.slots context.purseTask with
    | .present cell => some cell
    | _ => none)
    | return .error "dispatch payer purse unavailable"
  let some state := stateAt context.purseTask cell
    | return .error "dispatch payer purse state unavailable"
  if stateGeneration : state.generation = context.purseGeneration then
    if stateReserved : state.status = 3 ∨ state.status = 4 then
      if stateAmount : state.reserved = context.reserveAmount then
        if amountValid : 0 ≤ context.maximumCharge ∧
            context.maximumCharge ≤ context.reserveAmount then
          if commandExact : command =
              { subject := context.payerSubject
                nonce := payerNonce context
                targets := [AgentGrain.Operation.target .input context.purseTask
                  payerCapability cell.payload.root state (some payerObserve)] } then
            match ← DeclaredResourceController.prepareAuthenticated config.deployment config.profile
                ⟨config.federation, logicalHeight config opened.durable⟩ config.signature
                opened.ground command signed.authorityEnvelope with
            | .error _ => return .error "dispatch payer preparation refused"
            | .ok prepared =>
              if shape : DeclaredResourceController.PhysicalShape prepared then
                match ← DeclaredResourceController.admit config.signature prepared signed with
                | .error _ => return .error "dispatch payer native admission refused"
                | .ok accepted =>
                  if stateExact : stateAt context.purseTask cell = some state then
                    if physicalCurrent : ResourceBirthCodec.physicalRoot (.live cell) =
                        opened.durable.snapshot.model.roots ⟨context.purseTask⟩ then
                      return .ok ⟨signed, command, cell, state, stateExact,
                        payerCapability, payerObserve, prepared, shape, accepted,
                        commandExact, stateGeneration, stateReserved, stateAmount,
                        amountValid, physicalCurrent⟩
                    else return .error "dispatch payer physical root differs"
                  else return .error "dispatch payer state changed during inspection"
              else return .error "dispatch payer physical shape refused"
          else return .error "dispatch payer target/context mismatch"
        else return .error "dispatch payer charge exceeds hold"
      else return .error "dispatch payer held amount changed"
    else return .error "dispatch payer no longer reserved"
  else return .error "dispatch payer generation changed"

end Minidregg.Kernel.ApplicationDispatchAgentPayer
