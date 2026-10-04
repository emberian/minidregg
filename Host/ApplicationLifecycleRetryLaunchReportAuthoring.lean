/-
Source-owned physical report authoring for the versioned retry-CREATE
completion. The host supplies observations of its protected process and
volume; Mini derives the volume identity and canonical report/signing frames.
This is not physical attestation or native completion admission.
-/
import Kernel.ApplicationLifecycleRetryCompletionV4Report
import Host.ApplicationLifecycleLaunchReportAuthoring
import Host.ApplicationLifecycleCompletionAuthoring
import Kernel.ApplicationLifecycleRetryCompletionV4Ingress
import Kernel.ApplicationLifecycleResidentProfile

namespace Minidregg.Host.ApplicationLifecycleRetryLaunchReportAuthoring

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel

set_option autoImplicit false

/-- The typed host observation is the v3 one; only the claim it is bound to
and the report/signing frames differ. -/
abbrev PhysicalObservation := ApplicationLifecycleLaunchReportAuthoring.PhysicalObservation

private def decodeBegin (bytes : List UInt8) :
    Except String ApplicationLifecycleRetryBeginV4Ingress.Ingress := do
  let some begin := ApplicationLifecycleRetryBeginV4Ingress.codec.decode bytes
    | throw "noncanonical retry BEGIN-v4 ingress"
  unless begin.shape do throw "retry BEGIN-v4 shape refused"
  return begin

private def decodeReport (bytes : List UInt8) :
    Except String ApplicationLifecycleRetryCompletionV4Report.Report := do
  let some report := ApplicationLifecycleRetryCompletionV4Report.codec.decode bytes
    | throw "noncanonical retry physical report-v4"
  return report

/-- Derive a versioned physical report from the exact committed retry claim
and typed host observations. STOP audit bytes and the source volume ID are
encoded here; no caller-supplied serialized report or volume ID is accepted. -/
def reportPlan (beginBytes claimBytes : List UInt8)
    (observed : PhysicalObservation) :
    Except String ApplicationLifecycleRetryCompletionV4Report.Report := do
  let begin ← decodeBegin beginBytes
  let some claim := ApplicationLifecycleRetryClaimV4Projection.codec.decode claimBytes
    | throw "noncanonical committed retry claim-v4"
  unless claim.valid do throw "committed retry claim-v4 identity refused"
  unless claim.originalClaim.originalBegin == begin do
    throw "committed retry claim differs from BEGIN-v4"
  let stopAudit ← match observed.stopAudit with
    | some audit =>
        unless begin.begin.base.source.kind == .stop do
          throw "stop audit supplied for non-STOP operation"
        pure (ApplicationLifecycleCompletionReport.stopAuditCodec.encode audit)
    | none => pure []
  let volumeCustody := observed.volumeWitness.map fun witness =>
    ({ volume := begin.begin.volume, physicalWitness := witness } :
      ApplicationLifecycleLaunchBinding.Custody)
  let report : ApplicationLifecycleRetryCompletionV4Report.Report :=
    { claim := claim
      nonce := observed.nonce
      unit := observed.unit
      materializedImage := observed.materializedImage
      outcome := observed.outcome
      invocationId := observed.invocationId
      controlGroup := observed.controlGroup
      pid := observed.pid
      stopAudit := stopAudit
      installedManifest := ApplicationDispatchManifest.manifestCodec.encode
        (ApplicationLifecycleRetryBeginV4Ingress.prospectiveManifest begin)
      volumeCustody := volumeCustody }
  unless report.validFor begin do
    throw "physical report differs from selected BEGIN-v4/claim/volume"
  return report

/-- Return the exact bytes signed by the distinct physical custodian. -/
def signingPlan (beginBytes reportBytes : List UInt8) : Except String (List UInt8) := do
  let begin ← decodeBegin beginBytes
  let report ← decodeReport reportBytes
  unless report.validFor begin do throw "physical report differs from BEGIN-v4"
  return ApplicationLifecycleRetryCompletionV4Report.signingFrame
    begin.begin.base.domain begin.begin.base.semantics report

/-- Assemble the custodian's detached signature over the same exact report.
Verification under the configured custodian key is performed by native Mini. -/
def signedReport (beginBytes reportBytes signature : List UInt8) :
    Except String (List UInt8) := do
  let begin ← decodeBegin beginBytes
  let report ← decodeReport reportBytes
  unless report.validFor begin do throw "physical report differs from BEGIN-v4"
  unless signature.length == 64 do throw "physical signature must be 64 bytes"
  return ApplicationLifecycleRetryCompletionV4Report.signedCodec.encode
    { report := report, signature := signature }

/-- Current roots, capabilities and prior atom read by the operator. They are
candidates from signed native reads; fresh admission rechecks them. -/
abbrev CurrentObservation := ApplicationLifecycleCompletionAuthoring.CurrentObservation

/-- Source-owned retry completion source. The roots and prior atom are
candidates; op38 rechecks them against the current single durable image. -/
def sourcePlan (store : Minidregg.Theory.TypedAuthorization.Digest) (beginBytes claimIngressBytes signedReportBytes : List UInt8)
    (current : CurrentObservation) :
    Except String ApplicationLifecycleRetryCompletionV4Source.Source := do
  let begin ← decodeBegin beginBytes
  unless ApplicationLifecycleResidentProfile.beginMatchesV3 store begin.begin do
    throw "retry BEGIN-v4 is outside the resident signed-SPK physical hosting profile"
  let some claim := ApplicationLifecycleRetryClaimV4Ingress.codec.decode claimIngressBytes
    | throw "noncanonical retry claim-v4 ingress"
  let some physical := ApplicationLifecycleRetryCompletionV4Report.signedCodec.decode
      signedReportBytes
    | throw "noncanonical signed retry physical report-v4"
  let source : ApplicationLifecycleRetryCompletionV4Source.Source :=
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
  unless source.valid do throw "retry completion source identity mismatch"
  return source

private def decodeSource (sourceBytes : List UInt8) (domain semantics : Digest) :
    Except String ApplicationLifecycleRetryCompletionV4Source.Source := do
  let some source := ApplicationLifecycleRetryCompletionV4Source.codec.decode sourceBytes
    | throw "noncanonical retry completion source"
  unless source.valid do throw "retry completion source identity mismatch"
  unless domain == source.originalBegin.begin.base.domain &&
      semantics == source.originalBegin.begin.base.semantics do
    throw "retry completion profile differs from BEGIN-v4"
  return source

def commandPlan (domain semantics : Digest) (sourceBytes : List UInt8) :
    Except String (List UInt8) := do
  let source ← decodeSource sourceBytes domain semantics
  return DeclaredResourceController.commandCodec.encode (source.command domain semantics)

/-- Final canonical retry completion envelope. Equality with the
source-derived command prevents a signing-plan substitution; signatures,
current law, the consumed retry token and one-image CAS remain solely in
native admission. -/
def assemble (domain semantics : Digest) (sourceBytes signedCommandBytes
    packageObservationEnvelope : List UInt8) : Except String (List UInt8) := do
  let source ← decodeSource sourceBytes domain semantics
  let some signed := NativeHostCodec.signedInvocationStream.toLawful.decode signedCommandBytes
    | throw "noncanonical signed retry completion command"
  unless signed.commandBytes =
      DeclaredResourceController.commandCodec.encode (source.command domain semantics) do
    throw "signed command differs from retry completion source"
  return ApplicationLifecycleRetryCompletionV4Ingress.codec.encode
    { domain := domain
      semantics := semantics
      source := source
      signed := signed
      packageObservationEnvelope := packageObservationEnvelope }

end Minidregg.Host.ApplicationLifecycleRetryLaunchReportAuthoring
