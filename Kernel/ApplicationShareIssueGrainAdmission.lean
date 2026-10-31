/-
Current-image admission of one grain-backed ticket issue. The factory, Book,
tool settlement, parent witness and all their signatures are admitted by the
existing joint grain-birth checker. A separate current app delegation is
checked against the same loaded authority and directory before the ticket's
single empty allocation post is replaced by its source-derived initial atom.
-/
module

public import Kernel.ApplicationShareIssueGrainSource
public import Kernel.ApplicationShareIssueDelegation
public import Kernel.GrainResourceBirthAdmission

@[expose] public section

namespace Minidregg.Kernel.ApplicationShareIssueGrainAdmission

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.GrainResourceBirthController
open Minidregg.Theory
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.ApplicationShareIssueSource
open Minidregg.Kernel.ApplicationShareIssueGrainSource

set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local irreducible] NativeHost.Config.profile
  CanonicalRuntimeProfile.Profile.compilerProfile

variable {F : Type} [Field F] [DecidableEq F]

abbrev Durable := ResourceBirthController.Concrete.Durable
abbrev Ambient := DeclaredResourceController.Ambient

private theorem descriptorBytes_injective : Function.Injective
    (CanonicalCellRegistry.sourceEncoding.codec.encode :
      Descriptor CanonicalCellRegistry.registry → List UInt8) := by
  intro left right same
  have decoded := congrArg CanonicalCellRegistry.sourceEncoding.codec.decode same
  exact Option.some.inj (by
    simpa only [CanonicalCellRegistry.sourceEncoding.codec.decode_encode] using decoded)

structure Accepted {F : Type} [Field F] [DecidableEq F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : NativeHost.Config)
    (pins : FactoryPins) (ground : Minidregg.Compiler.ServedBasis.Ground config.deployment) (ambient : Ambient)
    (ingress : ApplicationShareIssueGrainSource.Ingress) where
  private mk ::
  decoded : GrainResourceBirthPolicyController.DecodedIngress
  grainBytes : decoded.bytes = ingress.grainIngress
  sourceReady : Ready config.deployment.domain ingress.spec
    (ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile
      config.deployment ingress.spec.issuer ingress.spec.ticket.issueNonce).value
  tariff : GrainResourceBirthController.Tariff
  birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
    config.deployment pins ground profile.semantics tariff decoded.source
  grain : GrainResourceBirthTransaction.PreparedTargets config.deployment
    ground.directory ground.authority
    profile.semantics ambient (decoded.source.grainCommand tariff)
  grainAccepted : GrainResourceBirthAdmission.Accepted profile config.deployment
    pins ground ambient tariff decoded.source birth grain decoded
  /-- The ticket descriptor under the platform record the grain birth was priced by. -/
  sourceDescriptor : decoded.source.birth =
    { sourceReady.expectedDescriptor profile config grainAccepted.pending.record
        ground.authority.authState ambient.height
        decoded.source.birth.fee.payer decoded.source.birth.funding with
      auxiliaryCreates := birth.prepared.authorityCombined.auxiliaryCreates }
  appPrepared : ApplicationShareIssueDelegation.Prepared
    ground
      profile config.federation ambient.height ingress.spec decoded.source.birth
  appChecked : ApplicationShareIssueDelegation.Checked appPrepared ingress.appEnvelope
  appReadOnly : ∀ guard ∈ ApplicationShareIssueDelegation.readGuards appPrepared, guard.cellId ∉
    (GrainResourceBirthTransaction.writes birth grain).map
      DurableDataIntent.DataWrite.cellId
theorem Accepted.sound {profile : CanonicalRuntimeProfile.Profile F}
    {config : NativeHost.Config} {pins : FactoryPins} {ground : Minidregg.Compiler.ServedBasis.Ground config.deployment}
    {ambient : Ambient} {ingress : ApplicationShareIssueGrainSource.Ingress}
    (accepted : Accepted profile config pins ground ambient ingress) :
    accepted.decoded.bytes = ingress.grainIngress ∧
    accepted.decoded.source.birth =
      { accepted.sourceReady.expectedDescriptor profile config
          accepted.grainAccepted.pending.record
          ground.authority.authState ambient.height
          accepted.decoded.source.birth.fee.payer accepted.decoded.source.birth.funding with
        auxiliaryCreates := accepted.birth.prepared.authorityCombined.auxiliaryCreates } :=
  ⟨accepted.grainBytes, accepted.sourceDescriptor⟩

private def refused : String := "grain-backed app share issue refused"

/-- The refusal names the admission stage that failed, behind the same stable prefix. Every stage
returned the one bare string before, so a refused ticket issue could not be told apart from any other. -/
private def refusedAt (stage : String) : String := refused ++ ": " ++ stage

/-- The stage text for the grain birth's own admission, with the reason it rejected. -/
private def grainRefusal {α : Type} (admitted : Except GrainResourceBirthAdmission.Reject α) : String :=
  match admitted with
  | .error reject => refusedAt ("grain birth admission: " ++ toString (repr reject))
  | .ok _ => refusedAt "grain birth admission"

def admitNative (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHost.Config) (pins : FactoryPins)
    (native : CredentialSignatureIO.NativeConfig)
    (ground : Minidregg.Compiler.ServedBasis.Ground config.deployment) (ambient : Ambient) (bytes : List UInt8) :
    IO (Except String
      (Σ ingress : ApplicationShareIssueGrainSource.Ingress,
        Accepted profile config pins ground ambient ingress)) := do
  let some ingress := ApplicationShareIssueGrainSource.codec.decode bytes
    | return .error (refusedAt "ingress decode")
  let some decoded := ingress.decodeGrain | return .error (refusedAt "grain ingress decode")
  let .ok sourceReady := ApplicationShareIssueSource.prepare profile config ingress.spec
    | return .error (refusedAt "source prepare")
  let some tariff := GrainResourceBirthAdmission.grainTariffAt config.deployment ground.view
    | return .error (refusedAt "grain tariff")
  let .ok birth := GrainResourceBirthController.prepareSourceBirth
      profile.compilerProfile profile.disabledEvaluators config.deployment pins ground
      profile.semantics tariff decoded.source ambient.height sourceReady.sourced | return .error (refusedAt "source birth prepare")
  let .ok grain := GrainResourceBirthTransaction.prepareTargets profile
      config.deployment pins ground ambient tariff decoded.source birth
    | return .error (refusedAt "birth targets prepare")
  let grainAdmission ← GrainResourceBirthAdmission.admitDecodedNative
      profile config.deployment pins ground ambient tariff decoded.source
      birth grain native decoded
  let .ok grainAccepted := grainAdmission | return .error (grainRefusal grainAdmission)
  if sourceDescriptorBytes :
      CanonicalCellRegistry.sourceEncoding.codec.encode decoded.source.birth =
        CanonicalCellRegistry.sourceEncoding.codec.encode
          { sourceReady.expectedDescriptor profile config grainAccepted.pending.record
              ground.authority.authState ambient.height
              decoded.source.birth.fee.payer decoded.source.birth.funding with
            auxiliaryCreates := birth.prepared.authorityCombined.auxiliaryCreates } then
    have sourceDescriptor : decoded.source.birth =
        { sourceReady.expectedDescriptor profile config grainAccepted.pending.record
            ground.authority.authState ambient.height
            decoded.source.birth.fee.payer decoded.source.birth.funding with
          auxiliaryCreates := birth.prepared.authorityCombined.auxiliaryCreates } :=
      descriptorBytes_injective sourceDescriptorBytes
    let context : ApplicationShareIssueDelegation.Context config.deployment :=
      ground
    let .ok appPrepared := ApplicationShareIssueDelegation.prepare context
        profile config.federation ambient.height ingress.spec decoded.source.birth
      | return .error (refusedAt "app delegation prepare")
    let .ok appChecked ← ApplicationShareIssueDelegation.check native appPrepared
        ingress.appEnvelope | return .error (refusedAt "app delegation check")
    if appReadOnly : ∀ guard ∈ ApplicationShareIssueDelegation.readGuards appPrepared, guard.cellId ∉
        (GrainResourceBirthTransaction.writes birth grain).map
          DurableDataIntent.DataWrite.cellId then
      if grainBytes : decoded.bytes = ingress.grainIngress then
        return .ok ⟨ingress,
          ⟨decoded, grainBytes, sourceReady,
            tariff, birth, grain, grainAccepted, sourceDescriptor,
            appPrepared, appChecked, appReadOnly⟩⟩
      else return .error (refusedAt "grain ingress bytes")
    else return .error (refusedAt "app delegation guard overlaps a birth write")
  else return .error (refusedAt "source descriptor differs from the expected one")

/-- The joint factory witness checks the same signed Book fee as the platform record's
creation-tariff quote on the whole ticket payload the factory judged. Grain settlement is a separate
permission-unit charge and cannot replace this conserved Book debit. -/
theorem Accepted.special_fee_bound {profile : CanonicalRuntimeProfile.Profile F}
    {config : NativeHost.Config} {pins : FactoryPins} {ground : Minidregg.Compiler.ServedBasis.Ground config.deployment}
    {ambient : Ambient} {ingress : ApplicationShareIssueGrainSource.Ingress}
    (accepted : Accepted profile config pins ground ambient ingress) :
    accepted.decoded.source.birth.fee.amount =
      accepted.decoded.source.birth.quotedFee accepted.grainAccepted.pending.record.creation := by
  have bound := accepted.grainAccepted.pending.checked.feeBound.1
  rw [accepted.grainAccepted.pending.priced] at bound
  exact bound

end Minidregg.Kernel.ApplicationShareIssueGrainAdmission
