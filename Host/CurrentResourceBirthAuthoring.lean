/-
Author an ordinary resource birth at the verifier-loaded native prefix. The
human JSON selects resource identities and funding; Host.Json constructs the
canonical cells, policies, grants and fee using current height and authority.
The genesis description is checked against the pinned runtime seed, never
treated as the current authority snapshot.
-/
import Host.Json
import Kernel.NativeHost

namespace Minidregg.Host.CurrentResourceBirthAuthoring

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.NativeObservationCodec
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Kernel

set_option autoImplicit false

/-- A current birth reveals its current height and issuer/policy epochs in the
authored grants. Require a sponsor-signed factory resource observation against
this exact opened image before deriving or returning those bytes. -/
def intentLoadedAuthorized (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (signedObservationBytes : List UInt8)
    (json : Lean.Json) : IO (Except String (List UInt8)) := do
  let refused := "resource birth observation refused"
  let some signed := signedCodec.decode signedObservationBytes
    | return .error refused
  match signed.challenge.intent.purpose with
  | .query query =>
      if query.kind != .object || query.target != config.deployment.factoryId ||
          query.view != .resource then
        return .error refused
  | .prepare _ => return .error refused
  match ← NativeObservationController.authorize config.signature
      (NativeHost.observationContext config opened) config.profile
      config.federation config.genesisHeight signed with
  | .error _ => return .error refused
  | .ok _ =>
      match Json.birthIntentFrom "$" json (fun path source =>
          Json.birthCurrent path source config
            (NativeHost.logicalHeight config opened.durable)
            opened.authority.snapshot.authState) with
      | .error reason => return .error reason
      | .ok intent =>
          if intent.subject != signed.challenge.intent.subject then
            return .error refused
          let .prepare (.birth birthBytes _) := intent.purpose
            | return .error refused
          let some descriptor :=
              (ResourceBirthCodec.descriptorCodec CanonicalCellRegistry.registry).decode birthBytes
            | return .error refused
          unless descriptor.createRequests.all (fun request =>
              match opened.directory.directory.slots request.cellId with
              | .absent => true
              | .present _ => false) do
            return .error refused
          return .ok (intentCodec.encode intent)

end Minidregg.Host.CurrentResourceBirthAuthoring
