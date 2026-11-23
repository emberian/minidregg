/-
Birth JSON supplies deployment coordinates, not an alternate runtime profile.
When authoring inside a configured Host, use that Host's complete profile after
checking the supplied coordinates. Optional runtime modes must not disappear
through reconstruction from a smaller JSON schema.
-/
module

public import Kernel.NativeHostContext

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Host.BirthRuntimeProfile

open Minidregg.Kernel
open Minidregg.Compiler

set_option autoImplicit false

/-- The runtime profile a birth source authors under. Against a deployed runtime, the
supplied genesis coordinates (deployment, federation, template, creation tariff, genesis
height) must be the deployed genesis's, and the deployed profile is used. The grain-birth
tariff is not compared: a composite carries today's price, which is the platform record's
(checked against the record by the loaded author and by the grain receiver), not the
genesis value the profile was derived from. -/
def select (supplied : NativeHost.Config) (deployed : Option NativeHost.Config) :
    Except String (CanonicalRuntimeProfile.Profile NativeHostProfile.Field) := do
  match deployed with
  | none => return supplied.profile
  | some config =>
      unless supplied.deployment == config.deployment &&
          supplied.federation == config.federation &&
          supplied.template == config.template &&
          supplied.tariff == config.tariff &&
          supplied.genesisHeight == config.genesisHeight do
        throw "birth source coordinates differ from the deployed runtime"
      return config.profile

/-- A JSON schema without the physical custodian field must still author
under the complete deployed profile, for every configured custodian key. -/
theorem select_without_custodian (config : NativeHost.Config) :
    select (NativeHost.Config.ofInputs { config.toInputs with completionCustodianKey := none })
      (some config) = .ok config.profile := by
  simp [select, NativeHost.Config.ofInputs, pure, Except.pure]

theorem select_unconfigured (config : NativeHost.Config) :
    select config none = .ok config.profile := by
  rfl

end Minidregg.Host.BirthRuntimeProfile
