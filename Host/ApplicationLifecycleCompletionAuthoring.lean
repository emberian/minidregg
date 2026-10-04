/-
Source-owned authoring for a physical lifecycle completion. The three stages
make the custodian sign the exact report before a management principal signs
the command derived from current native observations. None is admission.
-/
import Kernel.ApplicationLifecycleCompletionIngress
import Kernel.ApplicationLifecycleResidentProfile

namespace Minidregg.Host.ApplicationLifecycleCompletionAuthoring

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel

set_option autoImplicit false

structure PhysicalObservation where
  nonce : Nat
  unit : List UInt8
  materializedImage : List UInt8
  outcome : ApplicationLifecycleCompletionReport.Outcome
  invocationId : List UInt8
  controlGroup : List UInt8
  pid : Nat
  stopAudit : List UInt8

/-- Pin the raw op26 frame and derive the only installed-manifest bytes that
may appear in the custodian's report. `store` is the authoring Host's
`Config.expectedSeed` (every plan here checks the unit is this Store's). -/
def reportPlan (store : Digest) (beginBytes claimBytes : List UInt8)
    (observed : PhysicalObservation) : Except String ApplicationLifecycleCompletionReport.Report := do
  let some begin := ApplicationLifecycleBeginV2Ingress.codec.decode beginBytes
    | throw "noncanonical BEGIN-v2 ingress"
  unless ApplicationLifecycleResidentProfile.beginMatches store begin do
    throw "BEGIN-v2 is outside the resident signed-SPK physical hosting profile"
  let some claim := ApplicationLifecycleClaimProjection.codecV2.decode claimBytes
    | throw "noncanonical committed claim-v2 frame"
  let report : ApplicationLifecycleCompletionReport.Report :=
    { claim := claim
      nonce := observed.nonce
      unit := observed.unit
      materializedImage := observed.materializedImage
      outcome := observed.outcome
      invocationId := observed.invocationId
      controlGroup := observed.controlGroup
      pid := observed.pid
      stopAudit := observed.stopAudit
      installedManifest := ApplicationDispatchManifest.manifestCodec.encode
        (ApplicationLifecycleBeginV2Ingress.prospectiveManifest begin) }
  unless report.validFor begin do throw "physical report does not match BEGIN-v2"
  return report

def signingPlan (store domain semantics : Digest) (beginBytes reportBytes : List UInt8) :
    Except String (List UInt8) := do
  let some begin := ApplicationLifecycleBeginV2Ingress.codec.decode beginBytes
    | throw "noncanonical BEGIN-v2 ingress"
  unless ApplicationLifecycleResidentProfile.beginMatches store begin do
    throw "BEGIN-v2 is outside the resident signed-SPK physical hosting profile"
  let some report := ApplicationLifecycleCompletionReport.codec.decode reportBytes
    | throw "noncanonical physical report"
  unless report.validFor begin do throw "physical report does not match BEGIN-v2"
  unless domain == begin.base.domain && semantics == begin.base.semantics do
    throw "physical report signing profile differs from BEGIN-v2"
  return ApplicationLifecycleCompletionReport.signingFrame domain semantics report

/-- Packaging the custodian's detached signature is not signature verification.
The native receiver checks it under the configured public key. -/
def signedReport (store : Digest) (beginBytes reportBytes signature : List UInt8) :
    Except String (List UInt8) := do
  let some begin := ApplicationLifecycleBeginV2Ingress.codec.decode beginBytes
    | throw "noncanonical BEGIN-v2 ingress"
  unless ApplicationLifecycleResidentProfile.beginMatches store begin do
    throw "BEGIN-v2 is outside the resident signed-SPK physical hosting profile"
  let some report := ApplicationLifecycleCompletionReport.codec.decode reportBytes
    | throw "noncanonical physical report"
  unless report.validFor begin do throw "physical report does not match BEGIN-v2"
  unless signature.length == 64 do throw "physical signature must be 64 bytes"
  return ApplicationLifecycleCompletionReport.signedCodec.encode
    { report := report, signature := signature }

structure CurrentObservation where
  appRoot : Digest
  packageRoot : Digest
  appCapability : CapabilityId
  appObserveCapability : CapabilityId
  packageCapability : CapabilityId
  packageObserveCapability : CapabilityId
  packageAtomBefore : Option Minidregg.Theory.Hyperdocument.AtomRecord

/-- The roots and prior atom are candidates from signed native reads. Fresh
admission rechecks them against the current single durable image. -/
def sourcePlan (store : Digest) (beginBytes claimIngressBytes signedReportBytes : List UInt8)
    (current : CurrentObservation) :
    Except String ApplicationLifecycleCompletionSource.Source := do
  let some begin := ApplicationLifecycleBeginV2Ingress.codec.decode beginBytes
    | throw "noncanonical BEGIN-v2 ingress"
  unless ApplicationLifecycleResidentProfile.beginMatches store begin do
    throw "BEGIN-v2 is outside the resident signed-SPK physical hosting profile"
  let some claim := ApplicationLifecycleClaimV2Ingress.codec.decode claimIngressBytes
    | throw "noncanonical claim-v2 ingress"
  let some physical := ApplicationLifecycleCompletionReport.signedCodec.decode signedReportBytes
    | throw "noncanonical signed physical report"
  let source : ApplicationLifecycleCompletionSource.Source :=
    { originalBegin := begin
      originalClaim := claim
      physical := physical
      currentAppRoot := current.appRoot
      currentPackageRoot := current.packageRoot
      appCapability := current.appCapability
      appObserveCapability := current.appObserveCapability
      packageCapability := current.packageCapability
      packageObserveCapability := current.packageObserveCapability
      packageAtomBefore := current.packageAtomBefore }
  unless source.valid do throw "completion source identity mismatch"
  unless physical.report.validFor begin do throw "physical report does not match BEGIN-v2"
  return source

def commandPlan (domain semantics : Digest) (sourceBytes : List UInt8) :
    Except String (List UInt8) := do
  let some source := ApplicationLifecycleCompletionSource.codec.decode sourceBytes
    | throw "noncanonical completion source"
  unless source.valid do throw "completion source identity mismatch"
  unless domain == source.originalBegin.base.domain &&
      semantics == source.originalBegin.base.semantics do
    throw "completion profile differs from BEGIN-v2"
  return DeclaredResourceController.commandCodec.encode (source.command domain semantics)

/-- Package detached management/observation envelopes for the derived
command. This checks the incidence counts; native admission verifies every
signature and current policy under the installed profile. -/
def signedCommandPlan (commandBytes : List UInt8)
    (targetEnvelopes observeEnvelopes : List (List UInt8))
    (authorityEnvelope : List UInt8) : Except String (List UInt8) := do
  let some command := DeclaredResourceController.commandCodec.decode commandBytes
    | throw "noncanonical completion command"
  unless targetEnvelopes.length == command.targets.length do
    throw "completion target envelope count mismatch"
  unless observeEnvelopes.length ==
      (if command.requiresObservation then command.targets.length else 0) do
    throw "completion observation envelope count mismatch"
  return NativeHostCodec.signedInvocationStream.toLawful.encode
    { commandBytes := commandBytes
      targetEnvelopes := targetEnvelopes
      observeEnvelopes := observeEnvelopes
      authorityEnvelope := authorityEnvelope }

/-- Final canonical envelope. Equality with the source-derived command is
checked here to prevent a signing-plan substitution; signatures, current law,
and one-image CAS remain solely in native admission. -/
def assemble (domain semantics : Digest) (sourceBytes signedCommandBytes
    packageObservationEnvelope : List UInt8) : Except String (List UInt8) := do
  let some source := ApplicationLifecycleCompletionSource.codec.decode sourceBytes
    | throw "noncanonical completion source"
  unless source.valid do throw "completion source identity mismatch"
  unless domain == source.originalBegin.base.domain &&
      semantics == source.originalBegin.base.semantics do
    throw "completion profile differs from BEGIN-v2"
  let some signed := NativeHostCodec.signedInvocationStream.toLawful.decode signedCommandBytes
    | throw "noncanonical signed completion command"
  unless signed.commandBytes =
      DeclaredResourceController.commandCodec.encode (source.command domain semantics) do
    throw "signed command differs from completion source"
  return ApplicationLifecycleCompletionIngress.codec.encode
    { domain := domain
      semantics := semantics
      source := source
      signed := signed
      packageObservationEnvelope := packageObservationEnvelope }

theorem assembled_command_exact (domain semantics : Digest)
    (source : ApplicationLifecycleCompletionSource.Source)
    (signed : DeclaredResourceController.SignedCommand)
    (observe : List UInt8)
    (exact : signed.commandBytes =
      DeclaredResourceController.commandCodec.encode (source.command domain semantics)) :
    (ApplicationLifecycleCompletionIngress.Ingress.mk domain semantics source signed observe).signed.commandBytes =
      DeclaredResourceController.commandCodec.encode (source.command domain semantics) := exact

end Minidregg.Host.ApplicationLifecycleCompletionAuthoring
