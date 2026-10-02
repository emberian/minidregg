/- Canonical route-admission presentation. Private receiver provenance, not
this inspector's JSON, authenticates a current registration. -/
import Kernel.ApplicationRouteAdmission
import Host.ApplicationStreamContinuityInspection

namespace Minidregg.Host.ApplicationRouteAdmissionInspection

open Lean
open Minidregg.Kernel
open Minidregg.Kernel.ApplicationRouteAdmission
open Minidregg.Host.ApplicationStreamContinuityInspection
set_option autoImplicit false

def authorChallenge (config : NativeHost.Config) (json : Json) : Except String (List UInt8) := do
  let obj ← exactObject ["domain", "semantics", "app", "appGeneration", "session",
    "sessionGeneration", "subject", "ticketResource", "sessionKind", "registrationNonceHex"] json
  let domain ← nat (← field obj "domain")
  let semantics ← nat (← field obj "semantics")
  unless domain == config.deployment.domain.value && semantics == config.profile.semantics.value do
    throw "route namespace differs from pinned source"
  let nonce ← hex 32 (← field obj "registrationNonceHex")
  unless nonce.length == 32 do throw "route registration nonce must be 32 bytes"
  let kindString ← (← field obj "sessionKind").getStr?
  let kind ← match kindString with
    | "web" => pure ApplicationDispatchCodec.InterfaceKind.web
    | "api" => pure ApplicationDispatchCodec.InterfaceKind.api
    | _ => throw "route kind must be web or api"
  let selector : Selector :=
    { app := ← nat (← field obj "app")
      appGeneration := ← int (← field obj "appGeneration")
      session := ← nat (← field obj "session")
      sessionGeneration := ← int (← field obj "sessionGeneration")
      subject := ← nat (← field obj "subject")
      ticketResource := ← nat (← field obj "ticketResource")
      kind := kind }
  pure <| challengeCodec.encode
    ⟨config.deployment.domain, config.profile.semantics, selector, nonce⟩

def authorRequest (json : Json) : Except String (List UInt8) := do
  let obj ← exactObject ["challengeHex", "ingressHex"] json
  let challengeBytes ← hex 8192 (← field obj "challengeHex")
  let some challenge := challengeCodec.decode challengeBytes
    | throw "noncanonical route admission challenge"
  let ingress ← hex 12102760 (← field obj "ingressHex")
  unless !ingress.isEmpty do throw "empty route admission ingress"
  pure (requestCodec.encode ⟨challenge, ingress⟩)

def inspect (bytes : List UInt8) : Except String Json := do
  let some (challenge, b, tip) := attestationCodec.decode bytes
    | throw "noncanonical route admission attestation"
  pure <| .mkObj
    [("type", "application-route-admission-inspection-v1"),
     ("frameHex", hexJson bytes),
     ("challengeHex", hexJson (challengeCodec.encode challenge)),
     ("domain", decimal challenge.domain.value),
     ("semantics", decimal challenge.semantics.value),
     ("registrationNonceHex", hexJson challenge.registrationNonce),
     ("app", decimal b.app),
     ("appGeneration", signedDecimal b.appGeneration),
     ("session", decimal b.session),
     ("sessionGeneration", signedDecimal b.sessionGeneration),
     ("subject", decimal b.subject),
     ("ticketResource", decimal b.ticketResource),
     ("sessionKind", .str <| match challenge.selector.kind with | .web => "web" | .api => "api"),
     ("sessionFingerprint", decimal b.fingerprint.value),
     ("tip", .mkObj [("height", decimal tip.height),
       ("chain", decimal tip.chain.value), ("worldRoot", decimal tip.worldRoot.value)])]

end Minidregg.Host.ApplicationRouteAdmissionInspection
