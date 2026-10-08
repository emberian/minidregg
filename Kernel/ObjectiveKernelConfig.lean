/-
# Kernel.ObjectiveKernelConfig — a deployment's Objective policy as the kernel's configuration

The kernel families that run Objective package code inside a turn (the kernel
activity, `Kernel.ObjectiveActivity`; a seat contract's one-shot method,
`Kernel.SeatStore`) share one configuration, derived from the deployment's
Objective invocation policy (the `objectiveMethod` route binding the genesis
pins: `maximum`, `tariff`, `sourceBytes`). An operator who disabled Core4
(`objective-core4`) disables both with it. Fees are in the deployment's
creation-tariff asset, paid to its collector.
-/
import Kernel.ObjectiveActivity
import Kernel.ObjectiveBendNativeAdmission

namespace Minidregg.Kernel.ObjectiveKernelConfig

open Minidregg.Compiler
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.ObjectiveActivity (Config)

set_option autoImplicit false

abbrev Deployment := CanonicalCellRegistry.Deployment

/-- What the Host knows of the moment a kernel turn is decided in. -/
structure Ambient where
  federation : FederationId
  height : Height
  /-- The deployment's creation-tariff asset (the credit fees are paid in) and collector. -/
  asset : Nat
  collector : Nat

/-- The longest patience an await may declare. -/
def maxPatience : Nat := 64

/-- The storage deposit, in the deployment's credit asset, per byte of a retained
activity record: every yield reserves  in the purse. -/
def storageRate : Nat := 1

/-- The kernel configuration of a deployment: its Objective policy's envelope
ceilings, price and source bound, its Book and its credit; an await may be
abandoned `maxPatience` heights past its deadline. Refused when the
deployment registers no Objective policy or its operator disabled Core4. -/
def configOf {F : Type} [Field F] (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) : Except ObjectiveActivity.Refusal Config := do
  let some bytes := NativeInvocationProfile.binding profile.receiverParameters .objectiveMethod
    | throw (.packageType "this deployment registers no Objective policy")
  let some policy := ObjectiveBendNativeAdmission.decodePolicy bytes
    | throw (.packageType "this deployment's Objective policy does not decode")
  if ObjectiveBendNativeAdmission.evaluatorId ∈ profile.disabledEvaluators then
    throw (.packageType "the operator disabled objective-core4")
  pure { deployment := deployment, asset := ambient.asset, collector := ambient.collector
         limits := ObjectiveBendNativeAdmission.limits policy.maximum
         -- The extraction's tick budget is its own declared ceiling, never the source ceiling.
         planBudget := {ObjectiveBendNativeAdmission.budget policy.maximum with ticks := policy.maximum.extractTicks}
         maxTicks := policy.maximum.sourceTicks, maxExtractTicks := policy.extractTicksPerTurn,
         maxPatience := maxPatience
         typeFuel := policy.maximum.typeFuel, maxArtifactBytes := policy.sourceBytes
         tariff := policy.tariff
         abandonGrace := maxPatience, storageRate := storageRate }

end Minidregg.Kernel.ObjectiveKernelConfig
