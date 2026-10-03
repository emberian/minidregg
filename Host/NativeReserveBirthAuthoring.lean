/- Authenticated human/source authoring lives above the native kernel.
The kernel reserve factory, canonical codecs and receiving admission remain pure. -/
import Kernel.NativeHostReserveBirth
import Host.CurrentResourceBirthAuthoring

namespace Minidregg.Host.NativeReserveBirthAuthoring
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Theory
open Minidregg.Theory.ResourceBirth
open Minidregg.Kernel
open Minidregg.Kernel.NativeHostReserveBirth
set_option autoImplicit false

/-- Authenticated current-image authoring is a separate explicit method. No
JSON permission flag enters ordinary birth authoring. Capability identities are
names only; target, verbs, holder, ancestry and issuer template are source-derived. -/
def authorAndPrepareLoadedAuthorized (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (signedObservationBytes : List UInt8)
    (json : Lean.Json) (reserveCapabilityIds : List CapabilityId) :
    IO (Except String SigningPlan) := do
  match ← Minidregg.Host.CurrentResourceBirthAuthoring.intentLoadedAuthorized
      config opened signedObservationBytes json with
  | .error reason => return .error reason
  | .ok ordinaryIntentBytes =>
      let some intent := NativeObservationCodec.intentCodec.decode ordinaryIntentBytes
        | return .error "noncanonical ordinary birth intent"
      let .prepare (.birth ordinaryBytes sourceCapabilities) := intent.purpose
        | return .error "ordinary resource birth source required"
      let some ordinary := CanonicalCellRegistry.sourceEncoding.codec.decode ordinaryBytes
        | return .error "noncanonical ordinary birth source"
      match withReserveGrants config.profile.template opened.authority.snapshot.authState
          (NativeHost.logicalHeight config opened.durable) config.tariff ordinary reserveCapabilityIds with
      | .error reason => return .error reason
      | .ok descriptor =>
          return prepareLoaded config opened
            (CanonicalCellRegistry.sourceEncoding.codec.encode descriptor) sourceCapabilities

/-- Native wire adapter, exposing only the authenticated explicit source method. -/
def authorWireLoaded (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (bytes : List UInt8) : IO (Except String (List UInt8)) := do
  let some request := authorRequestCodec.decode bytes
    | return .error "noncanonical reserve birth author request"
  let some source := String.fromUTF8? request.sourceBytes.toByteArray
    | return .error "reserve birth source is not UTF-8"
  match Minidregg.Host.Json.parse source with
  | .error reason => return .error reason
  | .ok json =>
      return (← authorAndPrepareLoadedAuthorized config opened request.signedObservationBytes
        json request.reserveCapabilityIds).map signingPlanCodec.encode

end Minidregg.Host.NativeReserveBirthAuthoring
