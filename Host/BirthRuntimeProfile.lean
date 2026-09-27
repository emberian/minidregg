/-
Birth JSON supplies deployment coordinates, not an alternate runtime profile.
When authoring inside a configured Host, use that Host's complete profile after
checking the supplied coordinates. Optional runtime modes must not disappear
through reconstruction from a smaller JSON schema.
-/
import Kernel.NativeHostContext

namespace Minidregg.Host.BirthRuntimeProfile

open Minidregg.Kernel
open Minidregg.Compiler

set_option autoImplicit false

def select (supplied : NativeHost.Config) (deployed : Option NativeHost.Config) :
    Except String (CanonicalRuntimeProfile.Profile NativeHostProfile.Field) := do
  match deployed with
  | none => return supplied.profile
  | some config =>
      unless supplied.deployment == config.deployment &&
          supplied.federation == config.federation &&
          supplied.template == config.template &&
          supplied.tariff == config.tariff &&
          supplied.genesisHeight == config.genesisHeight &&
          supplied.grainBirthTariff == config.grainBirthTariff do
        throw "birth source coordinates differ from the deployed runtime"
      return config.profile

/-- A JSON schema without the physical custodian field must still author
under the complete deployed profile, for every configured custodian key. -/
theorem select_without_custodian (config : NativeHost.Config) :
    select { config with completionCustodianKey := none } (some config) =
      .ok config.profile := by
  simp [select]
  rfl

theorem select_unconfigured (config : NativeHost.Config) :
    select config none = .ok config.profile := by
  rfl

end Minidregg.Host.BirthRuntimeProfile
