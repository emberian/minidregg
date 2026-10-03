/- Native source-owned receiving entry points. This leaf is a next-cohort
consumer: BendReturnRelease must be registered in original-prefix semantic
history replay before it may append to a hosted world. Failed/uncertain paths
produce no release bytes. NativeHost.confirmed seals the actual journal prefix.
-/
import Kernel.NativeHost
import Kernel.BendReturnRelease

namespace Minidregg.Host.BendReceiving
open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.DeclaredResourceController
set_option autoImplicit false

inductive Result where
  | stored (receipt : NativeHostCodec.Receipt)
  | released (receipt : NativeHostCodec.Receipt) (bytes : List UInt8)
  | refused (detail : String)
  | uncertain (detail : String)

def sealStorage (config : NativeHost.Config) (command : Command)
    (signed : SignedCommand) : ReceiveResult → IO Result
  | .replayed record => do
      match ← NativeHost.confirmed config .replayed record.transactionId record.event.event.eventId with
      | .confirmed _ receipt => return .stored receipt
      | _ => return .uncertain "native source storage receipt readback refused"
  | .settlement (.confirmed kind _) => do
      match ← NativeHost.confirmed config kind
          (DeclaredResourceController.transactionId config.deployment.domain config.profile.semantics command)
          (DeclaredResourceController.invocationEvent config.deployment.domain config.profile.semantics command signed).eventId with
      | .confirmed _ receipt => return .stored receipt
      | _ => return .uncertain "native source storage receipt readback refused"
  | .transactionConflict => pure (.refused "native transaction identity conflict")
  | .unavailable detail => pure (.uncertain detail)
  | .settlement (.uncertain detail) | .settlement (.unavailable detail) => pure (.uncertain detail)
  | _ => pure (.refused "native source storage admission refused")

def publishSource (config : NativeHost.Config)
    (publication : BendSourcePublication.Publication) (signed : SignedCommand) : IO Result := do
  match ← NativeHost.openExisting config with
  | .error detail => return .uncertain detail
  | .ok opened =>
      let received ← BendSourcePublication.receiveLoaded config.deployment config.profile
        ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩
        config.signature config.transport opened.durable publication signed
      sealStorage config (BendSourcePublication.command publication) signed received

def storeOpaque (config : NativeHost.Config)
    (publication : BendOpaqueResultReceiver.Publication) (signed : SignedCommand) : IO Result := do
  match ← NativeHost.openExisting config with
  | .error detail => return .uncertain detail
  | .ok opened =>
      let received ← BendOpaqueResultReceiver.receiveLoaded config.deployment config.profile
        ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩
        config.signature config.transport opened.durable publication signed
      sealStorage config (BendOpaqueResultReceiver.command publication) signed received

/-- The complete retained result bytes are selected before CAS from the actual
current source root. Both event and native prefix are verified on readback;
there is no free-form Boolean receipt or caller-supplied plaintext substitute. -/
def release (config : NativeHost.Config) (bytes : List UInt8) : IO Result := do
  let some ingress := BendReturnRelease.ingressCodec.decode bytes
    | return .refused "noncanonical return release ingress"
  match ← NativeHost.openExisting config with
  | .error detail => return .uncertain detail
  | .ok opened =>
      let some (root, selected) := BendReturnRelease.currentResult
          (BendReturnRelease.sourceContext config opened) ingress.spec
        | return .refused "exact governed return is unavailable"
      if root != ingress.spec.source.root then
        return .refused "governed return source revision differs"
      match ← BendReturnRelease.receiveLoaded config opened bytes with
      | .confirmed kind receipt =>
          match ← NativeHost.openExisting config with
          | .error detail => return .uncertain detail
          | .ok readback =>
              if BendReturnRelease.replay readback ingress != some (.ok receipt) then
                return .uncertain "return release journal event differs"
              match ← NativeHost.confirmed config kind receipt.transactionId receipt.eventId with
              | .confirmed _ sealed => return .released sealed selected.result.bytes
              | _ => return .uncertain "return release original native prefix unavailable"
      | .unavailable detail | .uncertain detail => return .uncertain detail
      | _ => return .refused "current native return release refused"

end Minidregg.Host.BendReceiving
