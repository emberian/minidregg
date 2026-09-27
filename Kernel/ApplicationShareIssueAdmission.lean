/-
Native component admission for an app-governed share issue. The same loaded
image supplies the source-authored ticket birth and the current signed app
`.delegateObject` check. This module does not yet emit a durable special issue
intent or implement replay; callers must not treat Accepted as a receipt.
-/
import Kernel.ApplicationShareIssueDelegation
import Kernel.ResourceBirthReceiver

namespace Minidregg.Kernel.ApplicationShareIssueAdmission
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceBirth
open Minidregg.Kernel.ApplicationShareIssueSource
open Minidregg.Kernel.ResourceBirthPolicyController.Concrete
set_option autoImplicit false

variable {F : Type} [Field F] [DecidableEq F]
variable {profile : CanonicalRuntimeProfile.Profile F}
variable {config : NativeHost.Config} {pins : FactoryPins}
variable {durable : ResourceBirthController.Concrete.Durable} {height : Height}

/-- All components are minted by native verification on one `durable` and one
authority directory. The source descriptor equation rules out a bare birth of
caller-chosen ticket-looking bytes. A separate receiver must install a distinct
event and app read guard before this can authorize any dispatch. -/
structure Accepted (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHost.Config) (pins : FactoryPins)
    (durable : ResourceBirthController.Concrete.Durable) (height : Height)
    (ingress : ApplicationShareIssueSource.Ingress) where
  private mk ::
  sourceReady : Ready config.deployment.domain ingress.spec
    (ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile
      config.deployment ingress.spec.issuer ingress.spec.ticket.issueNonce).value
  birth : AcceptedBirth profile config.deployment pins durable height
  birthBytes : birth.ingress.bytes = ingress.birthIngress
  sourceDescriptor : birth.descriptor =
    { sourceReady.expectedDescriptor profile config
        birth.prepared.authority.snapshot.authState height
        birth.descriptor.fee.payer birth.descriptor.funding with
      auxiliaryCreates := birth.prepared.grants.auxiliaryCreates }
  appPrepared : ApplicationShareIssueDelegation.Prepared
    ⟨birth.prepared.directory, birth.prepared.authority⟩ profile config.federation
      height ingress.spec birth.descriptor
  appChecked : ApplicationShareIssueDelegation.Checked appPrepared ingress.appEnvelope
  appReadOnly : (ApplicationShareIssueDelegation.readGuard appPrepared).cellId ∉
    birth.prepared.writes.map DurableDataIntent.DataWrite.cellId

private def refused : String := "app share issue refused"

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
      (Σ ingress : ApplicationShareIssueSource.Ingress,
        Accepted profile config pins durable height ingress)) := do
  let some ingress := ApplicationShareIssueSource.ingressCodec.decode bytes
    | return .error refused
  let .ok ready := prepare profile config ingress.spec | return .error refused
  let some decoded := ResourceBirthPolicyController.Concrete.decodeIngress
      ingress.birthIngress | return .error refused
  let .ok birth ← ResourceBirthPolicyController.Concrete.admitDecodedNative
    profile config.deployment pins native durable height decoded
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
      let context : ApplicationShareIssueDelegation.Context config.deployment durable :=
        ⟨birth.prepared.directory, birth.prepared.authority⟩
      let .ok appPrepared := ApplicationShareIssueDelegation.prepare context
        profile config.federation height ingress.spec birth.descriptor
        | return .error refused
      let .ok appChecked ← ApplicationShareIssueDelegation.check native appPrepared
        ingress.appEnvelope | return .error refused
      if appReadOnly : (ApplicationShareIssueDelegation.readGuard appPrepared).cellId ∉
          birth.prepared.writes.map DurableDataIntent.DataWrite.cellId then
        return .ok ⟨ingress,
          ⟨ready, birth, birthBytes, sourceDescriptor, appPrepared,
            appChecked, appReadOnly⟩⟩
      else return .error refused
    else return .error refused
  else return .error refused

theorem Accepted.same_loaded_image {ingress : ApplicationShareIssueSource.Ingress}
    (accepted : Accepted profile config pins durable height ingress) :
    accepted.appPrepared.observed.before.payload.root = accepted.appPrepared.root :=
  accepted.appPrepared.observed.rootExact.symm

end Minidregg.Kernel.ApplicationShareIssueAdmission
