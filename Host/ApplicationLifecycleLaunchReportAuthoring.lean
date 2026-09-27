/-
Source-owned physical report authoring for launch-bound lifecycle completion.
The host supplies observations of its protected process and volume; Mini
derives the volume identity and canonical report/signing frames. This is not
physical attestation or native completion admission.
-/
import Kernel.ApplicationLifecycleCompletionV2Report

namespace Minidregg.Host.ApplicationLifecycleLaunchReportAuthoring

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
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
  /-- The operator's typed systemd/cgroup observation. Only STOP may carry it. -/
  stopAudit : Option ApplicationLifecycleCompletionReport.StopAudit
  /-- Exact protected-volume witness bytes, produced by the root-owned host
  checker. The source-derived volume ID is never supplied by the caller. -/
  volumeWitness : Option (List UInt8)

private def decodeBegin (bytes : List UInt8) :
    Except String ApplicationLifecycleBeginV3Ingress.Ingress := do
  let some begin := ApplicationLifecycleBeginV3Ingress.codec.decode bytes
    | throw "noncanonical launch BEGIN-v3 ingress"
  unless begin.shape do throw "launch BEGIN-v3 shape refused"
  return begin

private def decodeReport (bytes : List UInt8) :
    Except String ApplicationLifecycleCompletionV2Report.Report := do
  let some report := ApplicationLifecycleCompletionV2Report.codec.decode bytes
    | throw "noncanonical launch physical report-v2"
  return report

/-- Derive a versioned physical report from the exact committed claim and
typed host observations. STOP audit bytes and the source volume ID are encoded
here; no caller-supplied serialized report or volume ID is accepted. -/
def reportPlan (beginBytes claimBytes : List UInt8)
    (observed : PhysicalObservation) :
    Except String ApplicationLifecycleCompletionV2Report.Report := do
  let begin ← decodeBegin beginBytes
  let some claim := ApplicationLifecycleClaimV3Projection.codec.decode claimBytes
    | throw "noncanonical committed launch claim-v3"
  unless claim.valid do throw "committed launch claim-v3 identity refused"
  unless claim.originalClaim.originalBegin == begin do
    throw "committed launch claim differs from BEGIN-v3"
  let stopAudit ← match observed.stopAudit with
    | some audit =>
        unless begin.base.source.kind == .stop do
          throw "stop audit supplied for non-STOP operation"
        pure (ApplicationLifecycleCompletionReport.stopAuditCodec.encode audit)
    | none => pure []
  let volumeCustody := observed.volumeWitness.map fun witness =>
    ({ volume := begin.volume, physicalWitness := witness } :
      ApplicationLifecycleLaunchBinding.Custody)
  let report : ApplicationLifecycleCompletionV2Report.Report :=
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
        (ApplicationLifecycleBeginV3Ingress.prospectiveManifest begin)
      volumeCustody := volumeCustody }
  unless report.validFor begin do
    throw "physical report differs from selected BEGIN-v3/claim/volume"
  return report

/-- Return the exact bytes signed by the distinct physical custodian. -/
def signingPlan (beginBytes reportBytes : List UInt8) : Except String (List UInt8) := do
  let begin ← decodeBegin beginBytes
  let report ← decodeReport reportBytes
  unless report.validFor begin do throw "physical report differs from BEGIN-v3"
  return ApplicationLifecycleCompletionV2Report.signingFrame
    begin.base.domain begin.base.semantics report

/-- Assemble the custodian's detached signature over the same exact report.
Verification under the configured custodian key is performed by native Mini. -/
def signedReport (beginBytes reportBytes signature : List UInt8) :
    Except String (List UInt8) := do
  let begin ← decodeBegin beginBytes
  let report ← decodeReport reportBytes
  unless report.validFor begin do throw "physical report differs from BEGIN-v3"
  unless signature.length == 64 do throw "physical signature must be 64 bytes"
  return ApplicationLifecycleCompletionV2Report.signedCodec.encode
    { report := report, signature := signature }

end Minidregg.Host.ApplicationLifecycleLaunchReportAuthoring
