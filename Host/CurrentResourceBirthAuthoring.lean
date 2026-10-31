/-
Author an ordinary resource birth at the verifier-loaded native prefix. The
human JSON selects resource identities and funding; Host.Json constructs the
canonical cells, policies, grants and fee using current height and authority.
The genesis description is checked against the pinned runtime seed, never
treated as the current authority snapshot.
-/
module

public import Host.Json
public import Kernel.NativeHost

@[expose] public section

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
def intentAuthorizedOn (config : NativeHost.Config)
    (ground : Minidregg.Compiler.ServedBasis.Ground config.deployment) (signedObservationBytes : List UInt8)
    (json : Lean.Json) (providerRoutes : List (Nat × ProviderMetering.Schedule) := []) :
    IO (Except String (List UInt8)) := do
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
      ground config.profile
      config.federation config.genesisHeight signed with
  | .error _ => return .error refused
  | .ok _ =>
      let some current := PlatformCellDomain.recordOn config.deployment ground.view
        | return .error "platform cell unavailable: the image holds no platform record to price a birth from"
      match SourceAgreementJson.birthIntentFrom "$" json (fun path source =>
          SourceAgreementJson.birthCurrent path source config
            (config.genesisHeight + ground.height)
            ground.authority.authState
            (ResourceBirthPolicyController.Concrete.placementLineage ground.authority.cell)
            current providerRoutes) with
      | .error reason => return .error reason
      | .ok intent =>
          if intent.subject != signed.challenge.intent.subject then
            return .error refused
          let .prepare (.birth birthBytes _) := intent.purpose
            | return .error refused
          let some descriptor :=
              (ResourceBirthCodec.descriptorCodec CanonicalCellRegistry.registry).decode birthBytes
            | return .error refused
          if descriptor.creator != intent.subject then
            return .error refused
          -- Named, not folded into `refused`: a content-addressed cell (a Nock
          -- program) born twice meets exactly this, and must say so.
          unless descriptor.createRequests.all (fun request =>
              match ground.directory.slots request.cellId with
              | .absent => true
              | .present _ => false) do
            return .error "resource birth target already present"
          return .ok (intentCodec.encode intent)

/-- `intentAuthorizedOn` the full shape's ground of an opened image. -/
def intentLoadedAuthorized (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (signedObservationBytes : List UInt8)
    (json : Lean.Json) (providerRoutes : List (Nat × ProviderMetering.Schedule) := []) :
    IO (Except String (List UInt8)) :=
  intentAuthorizedOn config opened.ground signedObservationBytes json providerRoutes

end Minidregg.Host.CurrentResourceBirthAuthoring
