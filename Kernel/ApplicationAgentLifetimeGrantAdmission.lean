/-
Native component admission for an app-governed lifetime-grant issuance. The
same loaded image supplies the source-authored grant birth and the current
signed app `.delegateObject` check. This module does not yet emit a durable
special issue intent or implement replay; Accepted is not a receipt.
-/
import Kernel.ApplicationAgentLifetimeGrantDelegation
import Kernel.ResourceBirthReceiver

namespace Minidregg.Kernel.ApplicationAgentLifetimeGrantAdmission
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceBirth
open Minidregg.Kernel.ApplicationAgentLifetimeGrantSource
open Minidregg.Kernel.ResourceBirthPolicyController.Concrete
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {F : Type} [Field F] [DecidableEq F]
variable {profile : CanonicalRuntimeProfile.Profile F}
variable {config : NativeHost.Config} {pins : FactoryPins}
variable {durable : ResourceBirthController.Concrete.Durable} {height : Height}

/-- **The writes the issue commits**: the admitted birth's own, untransformed.
The issue's naming check (`Accepted.named`) runs over exactly these. -/
def finalWrites (birth : AcceptedBirth profile config.deployment pins durable height) :
    List DurableDataIntent.DataWrite :=
  birth.prepared.writes

/-- All components are minted by native verification on one `durable` and one
authority directory. The source descriptor equation rules out a bare birth of
caller-chosen grant-looking bytes. A separate receiver must install a distinct
event and app read guard before this can authorize any dispatch. -/
structure Accepted (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHost.Config) (pins : FactoryPins)
    (durable : ResourceBirthController.Concrete.Durable) (height : Height)
    (ingress : ApplicationAgentLifetimeGrantSource.Ingress) where
  private mk ::
  sourceReady : Ready config.deployment.domain ingress.spec
    (ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile
      config.deployment ingress.spec.grant.approval.issuer ingress.spec.grant.approval.nonce).value
  baseTariff : pins.tariff = config.tariff
  birth : AcceptedBirth profile config.deployment pins durable height
  birthBytes : birth.ingress.bytes = ingress.birthIngress
  sourceDescriptor : birth.descriptor =
    { sourceReady.expectedDescriptor profile config
        birth.prepared.authority.snapshot.authState height
        birth.descriptor.fee.payer birth.descriptor.funding with
      auxiliaryCreates := birth.prepared.grants.auxiliaryCreates }
  appPrepared : ApplicationAgentLifetimeGrantDelegation.Prepared
    (Minidregg.Compiler.ServedBasis.Ground.full _ birth.prepared.directory birth.prepared.authority) profile config.federation
      height ingress.spec birth.descriptor
  appChecked : ApplicationAgentLifetimeGrantDelegation.Checked appPrepared ingress.appEnvelope
  appReadOnly : ∀ guard ∈ ApplicationAgentLifetimeGrantDelegation.readGuards appPrepared, guard.cellId ∉
    birth.prepared.writes.map DurableDataIntent.DataWrite.cellId
  /-- Every birth write the issue commits is named by the admitted factory step. -/
  named : ResourceBirthController.Concrete.Named birth.factoryStep (finalWrites birth)

private def refused : String := "agent lifetime grant issue refused"

private theorem descriptorBytes_injective : Function.Injective
    (CanonicalCellRegistry.sourceEncoding.codec.encode :
      Descriptor CanonicalCellRegistry.registry → List UInt8) := by
  intro left right same
  have decoded := congrArg CanonicalCellRegistry.sourceEncoding.codec.decode same
  exact Option.some.inj (by
    simpa only [CanonicalCellRegistry.sourceEncoding.codec.decode_encode] using decoded)

def admitNative (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHost.Config) (pins : FactoryPins)
    (native : CredentialSignatureIO.NativeConfig)
    (durable : ResourceBirthController.Concrete.Durable) (height : Height)
    (bytes : List UInt8) : IO (Except String
      (Σ ingress : ApplicationAgentLifetimeGrantSource.Ingress,
        Accepted profile config pins durable height ingress)) := do
  let some ingress := ApplicationAgentLifetimeGrantSource.ingressCodec.decode bytes
    | return .error refused
  let .ok ready := prepare profile config ingress.spec | return .error refused
  if baseTariff : pins.tariff = config.tariff then
    let some decoded := ResourceBirthPolicyController.Concrete.decodeIngress
        ingress.birthIngress | return .error refused
    let .ok birth ← ResourceBirthPolicyController.Concrete.admitDecodedNative
        profile config.deployment pins native durable height decoded ready.sourced
        | return .error refused
    if birthBytes : birth.ingress.bytes = ingress.birthIngress then
      if sourceDescriptorBytes :
          CanonicalCellRegistry.sourceEncoding.codec.encode birth.descriptor =
            CanonicalCellRegistry.sourceEncoding.codec.encode
              { ready.expectedDescriptor profile config
                  birth.prepared.authority.snapshot.authState height
                  birth.descriptor.fee.payer birth.descriptor.funding with
                auxiliaryCreates := birth.prepared.grants.auxiliaryCreates } then
        have sourceDescriptor : birth.descriptor =
            { ready.expectedDescriptor profile config
                birth.prepared.authority.snapshot.authState height
                birth.descriptor.fee.payer birth.descriptor.funding with
              auxiliaryCreates := birth.prepared.grants.auxiliaryCreates } :=
          descriptorBytes_injective sourceDescriptorBytes
        let context : ApplicationAgentLifetimeGrantDelegation.Context config.deployment :=
          (Minidregg.Compiler.ServedBasis.Ground.full _ birth.prepared.directory birth.prepared.authority)
        let .ok appPrepared := ApplicationAgentLifetimeGrantDelegation.prepare context
          profile config.federation height ingress.spec birth.descriptor
          | return .error refused
        let .ok appChecked ← ApplicationAgentLifetimeGrantDelegation.check native appPrepared
          ingress.appEnvelope | return .error refused
        if appReadOnly : ∀ guard ∈ ApplicationAgentLifetimeGrantDelegation.readGuards appPrepared, guard.cellId ∉
            birth.prepared.writes.map DurableDataIntent.DataWrite.cellId then
          match ResourceBirthController.Concrete.checkNamed birth.factoryStep (finalWrites birth) with
          | .error cell => return .error s!"{refused}: neutralBirthUnjudged {cell}"
          | .ok named =>
            return .ok ⟨ingress,
              ⟨ready, baseTariff, birth, birthBytes,
                sourceDescriptor, appPrepared,
                appChecked, appReadOnly, named.down⟩⟩
        else return .error refused
      else return .error refused
    else return .error refused
  else return .error refused

theorem Accepted.same_loaded_image {ingress : ApplicationAgentLifetimeGrantSource.Ingress}
    (accepted : Accepted profile config pins durable height ingress) :
    accepted.appPrepared.observed.before.payload.root = accepted.appPrepared.root :=
  accepted.appPrepared.observed.rootExact.symm

/-- The ordinary factory checker and Book batch use the same signed fee, quoted
under the pinned tariff on the whole grant cell the factory judged. -/
theorem Accepted.special_fee_bound {ingress}
    (accepted : Accepted profile config pins durable height ingress) :
    accepted.birth.descriptor.fee.amount =
      accepted.birth.descriptor.quotedFee config.tariff := by
  have bound := accepted.birth.pending.checked.feeBound.1
  rw [accepted.baseTariff] at bound
  exact bound

/-- The grant cell, born with its initialized content, is a committed write. -/
theorem Accepted.grant_write_member {ingress}
    (accepted : Accepted profile config pins durable height ingress) :
    ResourceBirthController.birthWrite accepted.sourceReady.birth.create ∈ finalWrites accepted.birth := by
  apply accepted.birth.prepared.birth_write_member
  change accepted.sourceReady.birth ∈ accepted.birth.descriptor.births
  rw [accepted.sourceDescriptor]
  simp [Ready.expectedDescriptor, Ready.descriptor, Ready.births]

#assert_axioms Accepted.special_fee_bound Accepted.grant_write_member

end Minidregg.Kernel.ApplicationAgentLifetimeGrantAdmission
