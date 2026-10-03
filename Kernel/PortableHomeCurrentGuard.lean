/- High current-home guard AFTER actual ordinary controller acceptance.
The native source profile selects the home pin; neither a client statement nor
an archive chooses it. The signed Activity context must carry exactly the
projectionBytes indexing this guard, and its final Fits+DataIntent must retain
the returned whole-control ReadGuard alongside the current Activity guard.
Config.portableHomeControl source/profile registration is a required seam;
this WIP source cannot use a caller pin fallback while that seam is absent. -/
import Compiler.PortableHomeWorkerContext
import Kernel.NativeHostContext
import Kernel.DeclaredResourceController
namespace Minidregg.Kernel.PortableHomeCurrentGuard
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.PortableHomeWorkerContext
open Minidregg.Kernel.PortableHomeTransfer
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.NativeHost
set_option autoImplicit false

structure Guard (config : Config) (opened : Opened config) (projectionBytes : List UInt8) where
  private mk ::
  pin : PortableHomeTransferFrame.Pin
  sourceSelected : config.portableHomeControl = some pin
  state : State
  current : PortableHomeTransferFrame.readState pin
    (opened.durable.snapshot.canonicalBytes pin.cell) = some state
  projection : projectionCodec.decode projectionBytes = some (project pin state)
  credential : WorkerCredential
  credentialExact : credentialCodec.decode state.currentCredential = some credential
  allowed : DispatchAllowed state
  /-- Actual ordinary AcceptedInvocation source permission, not alleged signer bytes. -/
  authenticated : ∃ (command : Command) (signed : SignedCommand)
    (prepared : PreparedInvocation config.deployment config.profile
      ⟨config.federation,logicalHeight config opened.durable⟩ opened.durable command)
    (shape : PhysicalShape prepared) (accepted : AcceptedInvocation prepared signed),
    (accepted.dataIntent shape).subject = some credential.principal.subject ∧
    (accepted.checked none).receipt.prepared.controller.key.publicKey = credential.principal.publicKey

variable {config : Config} {opened : Opened config} {command : Command} {signed : SignedCommand}
  {prepared : PreparedInvocation config.deployment config.profile
    ⟨config.federation,logicalHeight config opened.durable⟩ opened.durable command}

def admit (projectionBytes : List UInt8) (shape : PhysicalShape prepared)
    (accepted : AcceptedInvocation prepared signed) : Option (Guard config opened projectionBytes) := do
  match sourceSelected : config.portableHomeControl with
  | none => none
  | some pin =>
    match current : PortableHomeTransferFrame.readState pin
        (opened.durable.snapshot.canonicalBytes pin.cell) with
    | none => none
    | some state =>
      if projection : projectionCodec.decode projectionBytes = some (project pin state) then
        match credentialExact : credentialCodec.decode state.currentCredential with
        | none => none
        | some credential =>
          if !credential.credentialId.isEmpty then
            if allowed : DispatchAllowed state then
              if subject : (accepted.dataIntent shape).subject = some credential.principal.subject then
                if key : (accepted.checked none).receipt.prepared.controller.key.publicKey = credential.principal.publicKey then
                  some ⟨pin,sourceSelected,state,current,projection,credential,credentialExact,allowed,
                    ⟨command,signed,prepared,shape,accepted,subject,key⟩⟩
                else none
              else none
            else none
          else none
      else none

def Guard.readGuard {config : Config} {opened : Opened config} {bytes : List UInt8}
    (guard : Guard config opened bytes) : ReadGuard :=
  ⟨guard.pin.cell,opened.durable.snapshot.model.roots guard.pin.cell⟩
theorem readGuard_current {config : Config} {opened : Opened config} {bytes : List UInt8}
    (guard : Guard config opened bytes) :
    guard.readGuard.expectedRoot = opened.durable.snapshot.model.roots guard.pin.cell := rfl
#assert_axioms readGuard_current
end Minidregg.Kernel.PortableHomeCurrentGuard
