/-
Source-owned application and session birth authoring against one verified native
image. The JSON parser supplies typed identities and funding; the loaded image
supplies current height and authority epochs. A genesis description is checked
against the pinned seed but never used as today's authority state.
-/
import Host.Json
import Kernel.NativeHost

namespace Minidregg.Host.ApplicationCurrentBirthAuthoring

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.NativeObservationCodec
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Kernel

set_option autoImplicit false

private def checkSource (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (context : Json.ApplicationBirthContext) : Except String Unit := do
  unless context.profile.template == config.profile.template &&
      context.source.deployment == config.deployment &&
      context.source.federation == config.federation &&
      context.source.tariff == config.tariff &&
      context.source.genesisHeight == config.genesisHeight do
    throw "application birth source differs from the pinned runtime"
  let built ← (NativeHostGenesis.build config.profile context.source).mapError
    (fun reason => s!"application birth genesis refused: {repr reason}")
  unless NativeHost.seedIdentity built.seed == config.expectedSeed do
    throw "application birth genesis differs from the pinned seed"
  unless context.height == NativeHost.logicalHeight config opened.durable do
    throw "application birth height is stale"

private def checkCompositeTariff (config : NativeHost.Config)
    (selected : Option NativeHost.GrainBirthTariffPin) : Except String Unit := do
  let _ ← config.grainBirthTariffValue
  unless selected == config.grainBirthTariff do
    throw "application grain birth tariff differs from the pinned runtime"

private def appDraft (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (path : String) (source : Lean.Json)
    (tariff : Option NativeHost.GrainBirthTariffPin) : Except String Draft := do
  checkCompositeTariff config tariff
  let (context, specJson) ← Json.applicationBirthContext path "application" source tariff
    (some (NativeHost.logicalHeight config opened.durable))
  checkSource config opened context
  let spec ← Json.applicationSpec (path ++ ".application") specJson
  let ready ← ApplicationGrainBirth.prepare spec
  let descriptor := ready.descriptorCurrent config.profile context.source
    opened.authority.snapshot.authState context.height context.creator context.nonce
    context.feePayer context.funding
  pure (.birth ((ResourceBirthCodec.descriptorCodec CanonicalCellRegistry.registry).encode
    descriptor) context.sourceCapabilities)

private def sessionDraft (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (path : String) (source : Lean.Json)
    (tariff : Option NativeHost.GrainBirthTariffPin) : Except String Draft := do
  checkCompositeTariff config tariff
  let (context, specJson) ← Json.applicationBirthContext path "session" source tariff
    (some (NativeHost.logicalHeight config opened.durable))
  checkSource config opened context
  let spec ← Json.applicationSessionSpec (path ++ ".session") specJson
  let ready ← ApplicationGrainSessionBirth.prepare spec
  let descriptor := ready.descriptorCurrent config.profile context.source
    opened.authority.snapshot.authState context.height context.creator context.nonce
    context.feePayer context.funding
  pure (.birth ((ResourceBirthCodec.descriptorCodec CanonicalCellRegistry.registry).encode
    descriptor) context.sourceCapabilities)

/-- A current app birth remains the same metered tool/parent composite as the
existing pure author, with its grant epochs rederived from `opened`. -/
def applicationIntentLoaded (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (json : Lean.Json) : Except String (List UInt8) := do
  let intent ← Json.grainBirthIntentFrom "$" "applicationGrainBirth"
    "applicationBirth" json (appDraft config opened)
  pure <| intentCodec.encode intent

def sessionIntentLoaded (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (json : Lean.Json) : Except String (List UInt8) := do
  let intent ← Json.grainBirthIntentFrom "$" "applicationSessionGrainBirth"
    "applicationSessionBirth" json (sessionDraft config opened)
  pure <| intentCodec.encode intent

end Minidregg.Host.ApplicationCurrentBirthAuthoring
