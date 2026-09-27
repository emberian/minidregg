/-
A source-owned wire for the physical custodian's lifecycle report. The
detached signature is checked against a key pinned by NativeHost.Config; this
module does not infer a systemd fact from a Boolean supplied by a caller.
Mini can verify the bytes and key, while truthful observation of the unit,
process and package remains an explicit host-custody assumption.
-/
import Kernel.ApplicationLifecycleBeginV2Ingress
import Kernel.ApplicationLifecycleClaimProjection
import Compiler.CredentialSignatureIO

namespace Minidregg.Kernel.ApplicationLifecycleCompletionReport

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-- Materialization, a running exact unit, and a completed stop audit are
distinct physical statements. No code is an admission result by itself. -/
inductive Outcome where
  | materialized | running | stopped
  deriving DecidableEq

def Outcome.code : Outcome → Nat
  | .materialized => 0
  | .running => 1
  | .stopped => 2

def Outcome.ofCode : Nat → Outcome
  | 0 => .materialized
  | 1 => .running
  | _ => .stopped

def outcomeStream : StreamCodec Outcome :=
  StreamCodec.xmap StreamCodec.nat Outcome.code Outcome.ofCode
    (by intro outcome; cases outcome <;> rfl)

/-- The custodian's signed stop observation records the systemd manager and
cgroup checks separately. These are attestations by the pinned operator; Mini
checks their exact shape and identity but cannot inspect systemd itself. -/
structure StopAudit where
  unit : List UInt8
  recordedInvocationId : List UInt8
  recordedControlGroup : List UInt8
  managerLoaded : Bool
  managerInactive : Bool
  managerMainPid : Nat
  managerJobEmpty : Bool
  managerInvocationCleared : Bool
  cgroupUnpopulated : Bool
  observationDigest : Digest
  deriving DecidableEq

def stopAuditStream : StreamCodec StopAudit :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream
      (StreamCodec.product bytesStream
        (StreamCodec.product bytesStream
          (StreamCodec.product StreamCodec.bool
            (StreamCodec.product StreamCodec.bool
              (StreamCodec.product StreamCodec.nat
                (StreamCodec.product StreamCodec.bool
                  (StreamCodec.product StreamCodec.bool
                    (StreamCodec.product StreamCodec.bool digestStream)))))))))
    (fun audit => (audit.unit, audit.recordedInvocationId,
      audit.recordedControlGroup, audit.managerLoaded, audit.managerInactive,
      audit.managerMainPid, audit.managerJobEmpty,
      audit.managerInvocationCleared, audit.cgroupUnpopulated,
      audit.observationDigest))
    (fun (unit, recordedInvocationId, recordedControlGroup, managerLoaded,
          managerInactive, managerMainPid, managerJobEmpty,
          managerInvocationCleared, cgroupUnpopulated, observationDigest) =>
      ⟨unit, recordedInvocationId, recordedControlGroup, managerLoaded,
        managerInactive, managerMainPid, managerJobEmpty,
        managerInvocationCleared, cgroupUnpopulated, observationDigest⟩)
    (by intro audit; cases audit; rfl)

def stopAuditFrame : List UInt8 :=
  "DREGG/APPLICATION/LIFECYCLE-STOP-AUDIT/v1".toUTF8.toList

def stopAuditCodec : LawfulCodec StopAudit :=
  NativeHostCodec.framed stopAuditFrame stopAuditStream

def stopAuditValid (unit invocationId controlGroup : List UInt8)
    (bytes : List UInt8) : Bool :=
  match stopAuditCodec.decode bytes with
  | none => false
  | some audit =>
      decide (audit.unit = unit ∧
        audit.recordedInvocationId = invocationId ∧
        audit.recordedControlGroup = controlGroup ∧
        audit.managerMainPid = 0) &&
      audit.managerLoaded && audit.managerInactive && audit.managerJobEmpty &&
        audit.managerInvocationCleared && audit.cgroupUnpopulated

/-- The exact claimed Mini projection is repeated verbatim in the signed
report. `stopAudit` is a bounded operator assertion, not Mini's own systemd
observation. The installed manifest must be the source-derived prospective
manifest for every operation, including start/stop. -/
structure Report where
  claim : ApplicationLifecycleClaimProjection.CommittedV2
  nonce : Nat
  unit : List UInt8
  materializedImage : List UInt8
  outcome : Outcome
  invocationId : List UInt8
  controlGroup : List UInt8
  pid : Nat
  stopAudit : List UInt8
  installedManifest : List UInt8
  deriving DecidableEq

def reportStream : StreamCodec Report :=
  StreamCodec.xmap
    (StreamCodec.product ApplicationLifecycleClaimProjection.committedV2Stream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product bytesStream
          (StreamCodec.product bytesStream
            (StreamCodec.product outcomeStream
              (StreamCodec.product bytesStream
                (StreamCodec.product bytesStream
                  (StreamCodec.product StreamCodec.nat
                    (StreamCodec.product bytesStream bytesStream)))))))))
    (fun report => (report.claim, report.nonce, report.unit, report.materializedImage,
      report.outcome, report.invocationId, report.controlGroup, report.pid,
      report.stopAudit, report.installedManifest))
    (fun (claim, nonce, unit, materializedImage, outcome, invocationId, controlGroup, pid,
          stopAudit, installedManifest) =>
      ⟨claim, nonce, unit, materializedImage, outcome, invocationId, controlGroup, pid,
        stopAudit, installedManifest⟩)
    (by intro report; cases report; rfl)

def frame : List UInt8 :=
  "DREGG/APPLICATION/LIFECYCLE-PHYSICAL-REPORT/v1".toUTF8.toList

def codec : LawfulCodec Report := NativeHostCodec.framed frame reportStream

def Report.canonicalBytes (report : Report) : List UInt8 := codec.encode report

theorem decoded_canonical {bytes : List UInt8} {report : Report}
    (decoded : codec.decode bytes = some report) :
    report.canonicalBytes = bytes :=
  NativeHostCodec.framed_canonical frame reportStream decoded

/-- Domain and installed semantics are included even though the claim also
commits them; this makes the custodian signature unambiguous across deployments. -/
def signingFrame (domain semantics : Digest) (report : Report) : List UInt8 :=
  "DREGG/APPLICATION/LIFECYCLE-PHYSICAL-SIGNATURE/v1".toUTF8.toList ++
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream bytesStream)).encode
      (domain, semantics, report.canonicalBytes)

def Report.validFor (report : Report)
    (begin : ApplicationLifecycleBeginV2Ingress.Ingress) : Bool :=
  let source := begin.base.source
  report.claim.valid &&
  decide (report.claim.core.source.begin = begin.base ∧
    report.claim.descriptor = begin.descriptor ∧
    report.nonce > 0 ∧
    report.unit = source.processIdentity ∧
    report.materializedImage = source.imageIdentity) &&
  !report.unit.isEmpty && decide (report.unit.length ≤ 256) &&
  decide (report.installedManifest =
    ApplicationDispatchManifest.manifestCodec.encode
      (ApplicationLifecycleBeginV2Ingress.prospectiveManifest begin)) &&
  match source.kind, report.outcome with
  | .install, .materialized | .upgrade, .materialized =>
      report.invocationId.isEmpty && report.controlGroup.isEmpty &&
        report.pid == 0 && report.stopAudit.isEmpty
  | .start, .running =>
      !report.invocationId.isEmpty && decide (report.invocationId.length ≤ 256) &&
        !report.controlGroup.isEmpty && decide (report.controlGroup.length ≤ 256) &&
        decide (report.pid > 0) && report.stopAudit.isEmpty
  | .stop, .stopped =>
      !report.invocationId.isEmpty && decide (report.invocationId.length ≤ 256) &&
        !report.controlGroup.isEmpty && decide (report.controlGroup.length ≤ 256) &&
        !report.stopAudit.isEmpty && decide (report.stopAudit.length ≤ 4096) &&
        report.pid == 0 &&
        stopAuditValid report.unit report.invocationId report.controlGroup report.stopAudit
  | _, _ => false

theorem wrong_begin_refused (report : Report)
    (begin : ApplicationLifecycleBeginV2Ingress.Ingress)
    (different : report.claim.core.source.begin ≠ begin.base) :
    report.validFor begin = false := by
  simp [Report.validFor, different]

structure Signed where
  report : Report
  signature : List UInt8
  deriving DecidableEq

def signedStream : StreamCodec Signed :=
  StreamCodec.xmap (StreamCodec.product reportStream bytesStream)
    (fun signed => (signed.report, signed.signature))
    (fun (report, signature) => ⟨report, signature⟩)
    (by intro signed; cases signed; rfl)

def signedFrame : List UInt8 :=
  "DREGG/APPLICATION/LIFECYCLE-PHYSICAL-SIGNED/v1".toUTF8.toList

def signedCodec : LawfulCodec Signed :=
  NativeHostCodec.framed signedFrame signedStream

/-- This certificate means only that the pinned custodian signed the exact
preimage and the source shape matches BEGIN. It does not by itself authorize
completion or establish current Mini state. -/
structure Checked (domain semantics : Digest) (publicKey : List UInt8)
    (begin : ApplicationLifecycleBeginV2Ingress.Ingress) where
  private mk ::
  signed : Signed
  shape : signed.report.validFor begin = true
  keyLength : publicKey.length = 32
  signatureLength : signed.signature.length = 64

def check (native : CredentialSignatureIO.NativeConfig)
    (domain semantics : Digest) (publicKey : List UInt8)
    (begin : ApplicationLifecycleBeginV2Ingress.Ingress) (signed : Signed) :
    IO (Except String (Checked domain semantics publicKey begin)) := do
  if keyLength : publicKey.length = 32 then
    if signatureLength : signed.signature.length = 64 then
      if shape : signed.report.validFor begin = true then
        match ← CredentialSignatureIO.verify native publicKey
            (signingFrame domain semantics signed.report) signed.signature with
        | .ok true => return .ok ⟨signed, shape, keyLength, signatureLength⟩
        | .ok false => return .error "physical custodian signature refused"
        | .error _ => return .error "physical custodian verifier unavailable"
      else return .error "physical report/source mismatch"
    else return .error "physical report signature length refused"
  else return .error "physical custodian public key length refused"

end Minidregg.Kernel.ApplicationLifecycleCompletionReport
