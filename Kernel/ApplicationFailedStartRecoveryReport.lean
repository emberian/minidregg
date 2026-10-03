/- Source-owned signed custody audit for the exact failed START incarnation. This does not prove that no earlier physical effect occurred. -/
import Kernel.ApplicationLifecycleClaimV3Projection
import Kernel.ApplicationLifecycleCompletionV2Report

namespace Minidregg.Kernel.ApplicationFailedStartRecoveryReport
open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.IntStream
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.Tower256ConcreteBackend
set_option autoImplicit false

structure Audit where
  app : Nat
  generation : Int
  operationId : Nat
  transactionId : Digest
  eventId : Digest
  imageIdentity : List UInt8
  unit : List UInt8
  recordedInvocationId : List UInt8
  recordedControlGroup : List UInt8
  recordPhase : List UInt8
  childPid : Option Nat
  managerLoaded : Bool
  managerActiveState : List UInt8
  managerMainPid : Nat
  managerJobEmpty : Bool
  managerInvocationId : List UInt8
  managerControlGroup : List UInt8
  recordedCgroupUnpopulated : Bool
  deriving DecidableEq

def auditStream : StreamCodec Audit :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat (StreamCodec.product intStream (StreamCodec.product StreamCodec.nat (StreamCodec.product digestStream (StreamCodec.product digestStream (StreamCodec.product bytesStream (StreamCodec.product bytesStream (StreamCodec.product bytesStream (StreamCodec.product bytesStream (StreamCodec.product bytesStream (StreamCodec.product (StreamCodec.option StreamCodec.nat) (StreamCodec.product StreamCodec.bool (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.bool (StreamCodec.product bytesStream (StreamCodec.product bytesStream StreamCodec.bool)))))))))))))))))
    (fun a => (a.app, (a.generation, (a.operationId, (a.transactionId, (a.eventId, (a.imageIdentity, (a.unit, (a.recordedInvocationId, (a.recordedControlGroup, (a.recordPhase, (a.childPid, (a.managerLoaded, (a.managerActiveState, (a.managerMainPid, (a.managerJobEmpty, (a.managerInvocationId, (a.managerControlGroup, a.recordedCgroupUnpopulated))))))))))))))))))
    (fun (app, (generation, (operationId, (transactionId, (eventId, (imageIdentity, (unit, (recordedInvocationId, (recordedControlGroup, (recordPhase, (childPid, (managerLoaded, (managerActiveState, (managerMainPid, (managerJobEmpty, (managerInvocationId, (managerControlGroup, recordedCgroupUnpopulated))))))))))))))))) => ⟨app, generation, operationId, transactionId, eventId, imageIdentity, unit, recordedInvocationId, recordedControlGroup, recordPhase, childPid, managerLoaded, managerActiveState, managerMainPid, managerJobEmpty, managerInvocationId, managerControlGroup, recordedCgroupUnpopulated⟩)
    (by intro a; cases a; rfl)

def Audit.validFor (audit : Audit)
    (claim : ApplicationLifecycleClaimV3Projection.Committed) : Bool :=
  let begin := claim.originalClaim.originalBegin
  let source := begin.base.source
  decide (audit.app = source.app ∧
    audit.generation = claim.core.source.before.generation ∧
    audit.operationId = source.operationId ∧
    audit.transactionId = claim.core.claimReceipt.transactionId ∧
    audit.eventId = claim.core.claimReceipt.eventId ∧
    audit.imageIdentity = source.imageIdentity ∧ audit.unit = source.processIdentity ∧
    audit.recordPhase = "entered".toUTF8.toList ∧ audit.childPid = none ∧
    audit.managerMainPid = 0) &&
  audit.managerLoaded && audit.managerJobEmpty && audit.recordedCgroupUnpopulated &&
  !audit.recordedInvocationId.isEmpty && decide (audit.recordedInvocationId.length ≤ 256) &&
  !audit.recordedControlGroup.isEmpty && decide (audit.recordedControlGroup.length ≤ 256) &&
  (audit.managerActiveState == "failed".toUTF8.toList ||
    audit.managerActiveState == "inactive".toUTF8.toList) &&
  (audit.managerInvocationId.isEmpty || audit.managerInvocationId == audit.recordedInvocationId) &&
  (audit.managerControlGroup.isEmpty || audit.managerControlGroup == audit.recordedControlGroup)

structure Report where
  claim : ApplicationLifecycleClaimV3Projection.Committed
  audit : Audit
  deriving DecidableEq

def reportStream : StreamCodec Report :=
  StreamCodec.xmap
    (StreamCodec.product ApplicationLifecycleClaimV3Projection.committedStream auditStream)
    (fun report => (report.claim, report.audit))
    (fun (claim, audit) => ⟨claim, audit⟩)
    (by intro report; cases report; rfl)

def frame : List UInt8 := "DREGG/APPLICATION/FAILED-START-REPORT/v1".toUTF8.toList

def codec : LawfulCodec Report := NativeHostCodec.framed frame reportStream

def Report.canonicalBytes (report : Report) : List UInt8 := codec.encode report

def Report.validFor (report : Report)
    (begin : ApplicationLifecycleBeginV3Ingress.Ingress) : Bool :=
  report.claim.valid &&
    decide (report.claim.originalClaim.originalBegin = begin ∧
      begin.base.source.kind = .start ∧
      (ApplicationLifecycleClaim.Kind.claimOperation .start).after
        report.claim.core.source.before =
          { report.claim.core.source.before with phase := 9 }) &&
    report.audit.validFor report.claim

structure Signed where
  report : Report
  signature : List UInt8
  deriving DecidableEq

def signedStream : StreamCodec Signed :=
  StreamCodec.xmap (StreamCodec.product reportStream bytesStream)
    (fun signed => (signed.report, signed.signature))
    (fun (report, signature) => ⟨report, signature⟩)
    (by intro signed; cases signed; rfl)

def signedCodec : LawfulCodec Signed := NativeHostCodec.framed
  "DREGG/APPLICATION/FAILED-START-SIGNED-REPORT/v1".toUTF8.toList signedStream

def signingFrame (domain semantics : Digest) (report : Report) : List UInt8 :=
  "DREGG/APPLICATION/FAILED-START-SIGNATURE/v1".toUTF8.toList ++
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream bytesStream)).encode
      (domain, semantics, report.canonicalBytes)

structure Checked (domain semantics : Digest) (publicKey : List UInt8)
    (begin : ApplicationLifecycleBeginV3Ingress.Ingress) where
  private mk ::
  signed : Signed
  shape : signed.report.validFor begin = true
  keyLength : publicKey.length = 32
  signatureLength : signed.signature.length = 64

def check (native : CredentialSignatureIO.NativeConfig)
    (domain semantics : Digest) (publicKey : List UInt8)
    (begin : ApplicationLifecycleBeginV3Ingress.Ingress) (signed : Signed) :
    IO (Except String (Checked domain semantics publicKey begin)) := do
  if keyLength : publicKey.length = 32 then
    if signatureLength : signed.signature.length = 64 then
      if shape : signed.report.validFor begin = true then
        match ← CredentialSignatureIO.verify native publicKey
            (signingFrame domain semantics signed.report) signed.signature with
        | .ok true => return .ok ⟨signed, shape, keyLength, signatureLength⟩
        | .ok false => return .error "failed START custodian signature refused"
        | .error _ => return .error "failed START custodian verifier unavailable"
      else return .error "failed START audit/original claim mismatch"
    else return .error "failed START signature length refused"
  else return .error "failed START custodian key length refused"

theorem wrong_begin_refused (report : Report)
    (begin : ApplicationLifecycleBeginV3Ingress.Ingress)
    (different : report.claim.originalClaim.originalBegin ≠ begin) :
    report.validFor begin = false := by
  simp [Report.validFor, different]

theorem child_present_refused (audit : Audit)
    (claim : ApplicationLifecycleClaimV3Projection.Committed)
    (pid : Nat) (present : audit.childPid = some pid) :
    audit.validFor claim = false := by
  simp [Audit.validFor, present]

theorem occupied_cgroup_refused (audit : Audit)
    (claim : ApplicationLifecycleClaimV3Projection.Committed)
    (occupied : audit.recordedCgroupUnpopulated = false) :
    audit.validFor claim = false := by
  simp [Audit.validFor, occupied]

theorem different_invocation_refused (audit : Audit)
    (claim : ApplicationLifecycleClaimV3Projection.Committed)
    (nonempty : audit.managerInvocationId.isEmpty = false)
    (different : audit.managerInvocationId ≠ audit.recordedInvocationId) :
    audit.validFor claim = false := by
  simp [Audit.validFor, nonempty, different]

theorem decode_encode (report : Report) :
    codec.decode report.canonicalBytes = some report := codec.decode_encode report

end Minidregg.Kernel.ApplicationFailedStartRecoveryReport
