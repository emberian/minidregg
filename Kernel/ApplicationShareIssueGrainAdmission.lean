/-
Current-image admission of one grain-backed ticket issue. The factory, Book,
tool settlement, parent witness and all their signatures are admitted by the
existing joint grain-birth checker. A separate current app delegation is
checked against the same loaded authority and directory before the ticket's
single empty allocation post is replaced by its source-derived initial atom.
-/
import Kernel.ApplicationShareIssueGrainSource
import Kernel.ApplicationShareIssueAtomicBirth
import Kernel.ApplicationShareIssueDelegation
import Kernel.GrainResourceBirthAdmission

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
    (pins : FactoryPins) (durable : Durable) (ambient : Ambient)
    (ingress : ApplicationShareIssueGrainSource.Ingress) where
  private mk ::
  decoded : GrainResourceBirthPolicyController.DecodedIngress
  grainBytes : decoded.bytes = ingress.grainIngress
  sourceReady : Ready config.deployment.domain ingress.spec
    (ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile
      config.deployment ingress.spec.issuer ingress.spec.ticket.issueNonce).value
  baseTariff : pins.tariff = config.tariff
  specialPins : FactoryPins
  specialPinsExact : specialPins = sourceReady.effectivePins pins
  tariff : GrainResourceBirthController.Tariff
  birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
    config.deployment specialPins durable profile.semantics tariff decoded.source
  sourceDescriptor : decoded.source.birth =
    { sourceReady.expectedDescriptor profile config
        birth.prepared.pre.authority.snapshot.authState ambient.height
        decoded.source.birth.fee.payer decoded.source.birth.funding with
      auxiliaryCreates := birth.prepared.authorityCombined.auxiliaryCreates }
  grain : GrainResourceBirthTransaction.PreparedTargets config.deployment
    birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
    profile.semantics ambient (decoded.source.grainCommand tariff)
  grainAccepted : GrainResourceBirthAdmission.Accepted profile config.deployment
    specialPins durable ambient tariff decoded.source birth grain decoded
  appPrepared : ApplicationShareIssueDelegation.Prepared
    ⟨birth.prepared.pre.directory, birth.prepared.pre.authority⟩
      profile config.federation ambient.height ingress.spec decoded.source.birth
  appChecked : ApplicationShareIssueDelegation.Checked appPrepared ingress.appEnvelope
  appReadOnly : (ApplicationShareIssueDelegation.readGuard appPrepared).cellId ∉
    (GrainResourceBirthTransaction.writes birth grain).map
      DurableDataIntent.DataWrite.cellId
  atomic : ApplicationShareIssueAtomicBirth.Checked sourceReady config.deployment
    (GrainResourceBirthTransaction.writes birth grain)

private def refused : String := "grain-backed app share issue refused"

def admitNative (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHost.Config) (pins : FactoryPins)
    (native : CredentialSignatureIO.NativeConfig)
    (durable : Durable) (ambient : Ambient) (bytes : List UInt8) :
    IO (Except String
      (Σ ingress : ApplicationShareIssueGrainSource.Ingress,
        Accepted profile config pins durable ambient ingress)) := do
  let some ingress := ApplicationShareIssueGrainSource.codec.decode bytes
    | return .error refused
  let some decoded := ingress.decodeGrain | return .error refused
  let .ok sourceReady := ApplicationShareIssueSource.prepare profile config ingress.spec
    | return .error refused
  if baseTariff : pins.tariff = config.tariff then
    let specialPins := sourceReady.effectivePins pins
    let .ok tariff := config.grainBirthTariffValue | return .error refused
    let .ok birth := GrainResourceBirthController.prepareSourceBirth
        profile.compilerProfile config.deployment specialPins durable profile.semantics
        tariff decoded.source | return .error refused
    if sourceDescriptorBytes :
        CanonicalCellRegistry.sourceEncoding.codec.encode decoded.source.birth =
          CanonicalCellRegistry.sourceEncoding.codec.encode
            { sourceReady.expectedDescriptor profile config
                birth.prepared.pre.authority.snapshot.authState ambient.height
                decoded.source.birth.fee.payer decoded.source.birth.funding with
              auxiliaryCreates := birth.prepared.authorityCombined.auxiliaryCreates } then
      have sourceDescriptor : decoded.source.birth =
          { sourceReady.expectedDescriptor profile config
              birth.prepared.pre.authority.snapshot.authState ambient.height
              decoded.source.birth.fee.payer decoded.source.birth.funding with
            auxiliaryCreates := birth.prepared.authorityCombined.auxiliaryCreates } :=
        descriptorBytes_injective sourceDescriptorBytes
      let .ok grain := GrainResourceBirthTransaction.prepareTargets profile
          config.deployment specialPins durable ambient tariff decoded.source birth
        | return .error refused
      let .ok grainAccepted ← GrainResourceBirthAdmission.admitDecodedNative
          profile config.deployment specialPins durable ambient tariff decoded.source
          birth grain native decoded | return .error refused
      let context : ApplicationShareIssueDelegation.Context config.deployment durable :=
        ⟨birth.prepared.pre.directory, birth.prepared.pre.authority⟩
      let .ok appPrepared := ApplicationShareIssueDelegation.prepare context
          profile config.federation ambient.height ingress.spec decoded.source.birth
        | return .error refused
      let .ok appChecked ← ApplicationShareIssueDelegation.check native appPrepared
          ingress.appEnvelope | return .error refused
      if appReadOnly : (ApplicationShareIssueDelegation.readGuard appPrepared).cellId ∉
          (GrainResourceBirthTransaction.writes birth grain).map
            DurableDataIntent.DataWrite.cellId then
        match ApplicationShareIssueAtomicBirth.check sourceReady config.deployment
            (GrainResourceBirthTransaction.writes birth grain) with
        | none => return .error refused
        | some atomic =>
            if grainBytes : decoded.bytes = ingress.grainIngress then
              return .ok ⟨ingress,
                ⟨decoded, grainBytes, sourceReady, baseTariff, specialPins,
                  rfl, tariff, birth, sourceDescriptor, grain,
                  grainAccepted, appPrepared, appChecked, appReadOnly, atomic⟩⟩
            else return .error refused
      else return .error refused
    else return .error refused
  else return .error refused

/-- The joint factory witness checks the same signed Book fee as the
source-derived full ticket payload quote. Grain settlement is a separate
permission-unit charge and cannot replace this conserved Book debit. -/
theorem Accepted.special_fee_bound {profile : CanonicalRuntimeProfile.Profile F}
    {config : NativeHost.Config} {pins : FactoryPins} {durable : Durable}
    {ambient : Ambient} {ingress : ApplicationShareIssueGrainSource.Ingress}
    (accepted : Accepted profile config pins durable ambient ingress) :
    accepted.decoded.source.birth.fee.amount =
      accepted.decoded.source.birth.quotedFee
        (accepted.sourceReady.effectiveTariff config.tariff) := by
  have bound := accepted.grainAccepted.pending.checked.feeBound.1
  have tariffExact : accepted.specialPins.tariff =
      accepted.sourceReady.effectiveTariff pins.tariff := by
    exact congrArg FactoryPins.tariff accepted.specialPinsExact
  rw [tariffExact] at bound
  rw [accepted.baseTariff] at bound
  exact bound

end Minidregg.Kernel.ApplicationShareIssueGrainAdmission
