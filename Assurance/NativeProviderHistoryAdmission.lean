/- Focused executable predicates plus the real credential receiving gate.
These fixtures do not fabricate a verified Store or claim native receipt evidence.
The shared-Store journey separately exercises history replay and append races. -/
import Kernel.NativePlanHeight
import Kernel.NativeProviderHistory

namespace Minidregg.Assurance.NativeProviderHistoryAdmission

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Kernel
open Minidregg.Kernel.CredentialSignedEnvelopeController
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

def key : KeyRecord := ⟨1, 0, 1, 9, [1, 2, 3], 0, 100, none⟩
def registry : KeyRegistryProjection := ⟨registryCodecVersion, ⟨7⟩, 0, [key]⟩
def header : SignedHeader :=
  ⟨envelopeCodecVersion, [4, 5], 80, 1, 0, 1, [6], [7, 8], 99⟩
def state (height : Nat) : ControllerState :=
  ⟨stateCodecVersion, ⟨7⟩, registryDigest (registryCodec.encode registry),
    0, header.footprint, height, []⟩
def prepareAt (height : Nat) (h : SignedHeader) :
    Except (Failure Unit) Prepared :=
  prepare 9 header.domain header.message (stateCodec.encode (state height))
    (registryCodec.encode registry) (envelopeCodec.encode ⟨h, [9]⟩)
def acceptedAt (height : Nat) (h : SignedHeader) : Bool :=
  match prepareAt height h with | .ok _ => true | .error _ => false
def expiredAt (height : Nat) (h : SignedHeader) : Bool :=
  match prepareAt height h with | .error .expired => true | _ => false

-- Actual receiving parser accepts this unsigned fixture through semantic
-- preparation only; cryptographic finish is intentionally not fabricated.
#guard acceptedAt 20 (NativePlanHeight.pinHeader 20 header)
#guard expiredAt 21 (NativePlanHeight.pinHeader 20 header)
#guard acceptedAt 21 header
#guard expiredAt 20 (NativePlanHeight.pinHeader 20 { header with validUntil := 19 })
#guard (NativePlanHeight.pinHeader 20 header).message == header.message
#guard (NativePlanHeight.pinHeader 20 header).nullifier == header.nullifier

def before : ProviderRoute.State := ⟨⟨1, 1, 12, 0⟩, 0⟩
def held : ProviderRoute.State := ProviderRoute.after (.reserve 3) 3 before
def reserveCommand : DeclaredResourceController.Command :=
  { subject := ⟨9⟩, nonce := 101,
    targets := [ProviderRoute.target (.reserve 3) 3 8974 ⟨103⟩ ⟨10⟩ before] }
def fenceCommand : DeclaredResourceController.Command :=
  { subject := ⟨9⟩, nonce := 102,
    targets := [ProviderRoute.target .disconnect 3 8974 ⟨103⟩ ⟨11⟩ held] }
def call (command : DeclaredResourceController.Command) : List UInt8 :=
  callCodec.encode (.invoke ⟨DeclaredResourceController.commandCodec.encode command, [], [], []⟩)

#guard NativeProviderHistory.exactHardFence ⟨8974⟩ (call reserveCommand) (call fenceCommand)
def parentWitness : DeclaredResourceController.Target :=
  AgentGrain.Operation.input.target 8971 ⟨75⟩ ⟨12⟩ ⟨1, 4, 997, 3⟩
#guard NativeProviderHistory.exactHardFence ⟨8974⟩
  (call { reserveCommand with targets := parentWitness :: reserveCommand.targets }) (call fenceCommand)
#guard !NativeProviderHistory.exactHardFence ⟨8974⟩
  (call { reserveCommand with targets :=
    [ProviderRoute.target .input 3 8974 ⟨103⟩ ⟨10⟩ held] }) (call fenceCommand)
#guard !NativeProviderHistory.exactHardFence ⟨8974⟩
  (call { reserveCommand with targets :=
    AgentGrain.Operation.cancel.target 8971 ⟨75⟩ ⟨12⟩ ⟨1, 4, 997, 3⟩ :: reserveCommand.targets })
  (call fenceCommand)
#guard !NativeProviderHistory.exactHardFence ⟨8975⟩ (call reserveCommand) (call fenceCommand)
#guard !NativeProviderHistory.exactHardFence ⟨8974⟩ (call reserveCommand)
  (call { fenceCommand with subject := ⟨20⟩ })
#guard !NativeProviderHistory.exactHardFence ⟨8974⟩ (call reserveCommand)
  (call { fenceCommand with targets :=
    [ProviderRoute.target (.settle 3) 3 8974 ⟨103⟩ ⟨11⟩ held] })
#guard !NativeProviderHistory.exactHardFence ⟨8974⟩ (call reserveCommand)
  (call { fenceCommand with targets := fenceCommand.targets ++ reserveCommand.targets })

def plan : SigningPlan :=
  ⟨⟨1⟩, ⟨2⟩, ⟨3⟩, 20,
    .invoke (DeclaredResourceController.commandCodec.encode reserveCommand),
    [⟨4, 0, headerCodec.encode header⟩, ⟨1, 0, headerCodec.encode header⟩]⟩
def pinnedPlanCorrect : Bool :=
  match NativePlanHeight.pin plan with
  | .error _ => false
  | .ok pinned =>
      decide (pinned.domain = plan.domain) && decide (pinned.semantics = plan.semantics) &&
      decide (pinned.worldRoot = plan.worldRoot) && pinned.height == plan.height &&
      (draftCodec.encode pinned.finalizedDraft == draftCodec.encode plan.finalizedDraft) &&
      pinned.slots.length == 2 && pinned.slots.all (fun slot =>
        decide (headerCodec.decode slot.header = some (NativePlanHeight.pinHeader 20 header)))
#guard pinnedPlanCorrect
def pinRefused (candidate : SigningPlan) : Bool :=
  match NativePlanHeight.pin candidate with | .error _ => true | .ok _ => false
#guard pinRefused { plan with slots := [] }
#guard pinRefused { plan with slots := [⟨4, 0, []⟩, ⟨1, 0, []⟩] }
#guard pinRefused { plan with finalizedDraft := .invoke [] }

end Minidregg.Assurance.NativeProviderHistoryAdmission
