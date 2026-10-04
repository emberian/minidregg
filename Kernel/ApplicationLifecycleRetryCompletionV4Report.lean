/-
Physical custodian report retaining the full governed v4 repeat-CREATE claim. The host signs the
exact selected command digest and the protected persistent-volume mapping
alongside its process observation. Mini checks the signed shape and current
authority; it cannot inspect the OS or infer execution from a receipt.
-/
import Kernel.ApplicationLifecycleRetryClaimV4Projection
import Kernel.ApplicationLifecycleCompletionReport

namespace Minidregg.Kernel.ApplicationLifecycleRetryCompletionV4Report

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

structure Report where
  claim : ApplicationLifecycleRetryClaimV4Projection.Committed
  nonce : Nat
  unit : List UInt8
  materializedImage : List UInt8
  outcome : ApplicationLifecycleCompletionReport.Outcome
  invocationId : List UInt8
  controlGroup : List UInt8
  pid : Nat
  stopAudit : List UInt8
  installedManifest : List UInt8
  /-- Signed host observation of the protected volume mapping. The host
  checks the actual volume path and custody metadata; Mini only binds these
  exact bytes to the kernel volume ID and earlier completed creation. -/
  volumeCustody : Option ApplicationLifecycleLaunchBinding.Custody
  deriving DecidableEq

def reportStream : StreamCodec Report :=
  StreamCodec.xmap
    (StreamCodec.product ApplicationLifecycleRetryClaimV4Projection.committedStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product bytesStream
          (StreamCodec.product bytesStream
            (StreamCodec.product ApplicationLifecycleCompletionReport.outcomeStream
              (StreamCodec.product bytesStream
                (StreamCodec.product bytesStream
                  (StreamCodec.product StreamCodec.nat
                    (StreamCodec.product bytesStream
                      (StreamCodec.product bytesStream
                        (StreamCodec.option ApplicationLifecycleLaunchBinding.custodyStream)))))))))))
    (fun report => (report.claim, report.nonce, report.unit,
      report.materializedImage, report.outcome, report.invocationId,
      report.controlGroup, report.pid, report.stopAudit,
      report.installedManifest, report.volumeCustody))
    (fun (claim, nonce, unit, materializedImage, outcome, invocationId,
          controlGroup, pid, stopAudit, installedManifest, volumeCustody) =>
      ⟨claim, nonce, unit, materializedImage, outcome, invocationId,
        controlGroup, pid, stopAudit, installedManifest, volumeCustody⟩)
    (by intro report; cases report; rfl)

def frame : List UInt8 :=
  "DREGG/APPLICATION/RETRY-CREATE-PHYSICAL-REPORT/v4".toUTF8.toList

def codec : LawfulCodec Report := NativeHostCodec.framed frame reportStream

def Report.canonicalBytes (report : Report) : List UInt8 := codec.encode report

def Report.custodyContinuous (report : Report)
    (begin : ApplicationLifecycleRetryBeginV4Ingress.Ingress) : Bool :=
  match begin.start with
  | some binding => match binding.choice, binding.priorCreate with
      | .continue, some (_, oldCustody) =>
          report.volumeCustody == some oldCustody
      | .create _, none =>
          match report.volumeCustody with
          | some custody => custody.validFor begin.volume
          | none => false
      | _, _ => false
  | none =>
      match begin.base.source.kind, report.volumeCustody with
      | .install, none | .upgrade, none => true
      | .stop, some custody => custody.validFor begin.volume
      | _, _ => false

theorem continue_custody_exact (report : Report)
    (begin : ApplicationLifecycleRetryBeginV4Ingress.Ingress)
    (binding : ApplicationLifecycleLaunchBinding.Binding)
    (receipt : NativeHostCodec.Receipt)
    (custody : ApplicationLifecycleLaunchBinding.Custody)
    (selected : begin.start = some binding)
    (choice : binding.choice = .continue)
    (prior : binding.priorCreate = some (receipt, custody))
    (valid : report.custodyContinuous begin = true) :
    report.volumeCustody = some custody := by
  simpa [Report.custodyContinuous, selected, choice, prior] using valid

def Report.validFor (report : Report)
    (begin : ApplicationLifecycleRetryBeginV4Ingress.Ingress) : Bool :=
  let source := begin.base.source
  report.claim.valid &&
    decide (report.claim.originalClaim.originalBegin = begin ∧
      report.nonce > 0 ∧ report.unit = source.processIdentity ∧
      report.materializedImage = source.imageIdentity) &&
    !report.unit.isEmpty && decide (report.unit.length ≤ 256) &&
    report.custodyContinuous begin &&
    decide (report.installedManifest =
      ApplicationDispatchManifest.manifestCodec.encode
        (ApplicationLifecycleRetryBeginV4Ingress.prospectiveManifest begin)) &&
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
        ApplicationLifecycleCompletionReport.stopAuditValid report.unit
          report.invocationId report.controlGroup report.stopAudit
    | _, _ => false

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
  "DREGG/APPLICATION/RETRY-CREATE-PHYSICAL-SIGNED/v4".toUTF8.toList

def signedCodec : LawfulCodec Signed :=
  NativeHostCodec.framed signedFrame signedStream

def signingFrame (domain semantics : Digest) (report : Report) : List UInt8 :=
  "DREGG/APPLICATION/RETRY-CREATE-PHYSICAL-SIGNATURE/v4".toUTF8.toList ++
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream bytesStream)).encode
      (domain, semantics, report.canonicalBytes)

theorem decode_encode (report : Report) :
    codec.decode report.canonicalBytes = some report := codec.decode_encode report

theorem decoded_canonical {bytes : List UInt8} {report : Report}
    (decoded : codec.decode bytes = some report) :
    report.canonicalBytes = bytes :=
  NativeHostCodec.framed_canonical frame reportStream decoded

theorem wrong_begin_refused (report : Report)
    (begin : ApplicationLifecycleRetryBeginV4Ingress.Ingress)
    (different : report.claim.originalClaim.originalBegin ≠ begin) :
    report.validFor begin = false := by
  simp [Report.validFor, different]

/-- Cryptographic custody over the exact action, volume and process report.
The signature proves who attested it; the native host remains responsible for
truthfully checking its protected volume and systemd process. -/
structure Checked (domain semantics : Digest) (publicKey : List UInt8)
    (begin : ApplicationLifecycleRetryBeginV4Ingress.Ingress) where
  private mk ::
  signed : Signed
  shape : signed.report.validFor begin = true
  keyLength : publicKey.length = 32
  signatureLength : signed.signature.length = 64

def check (native : CredentialSignatureIO.NativeConfig)
    (domain semantics : Digest) (publicKey : List UInt8)
    (begin : ApplicationLifecycleRetryBeginV4Ingress.Ingress) (signed : Signed) :
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

end Minidregg.Kernel.ApplicationLifecycleRetryCompletionV4Report
