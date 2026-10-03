/- Source-derived recovery command for an original START and claimed generation. Recovery advances only to stopped through the installed reconciliation law; no package write or created-volume marker is produced. -/
import Kernel.ApplicationFailedStartRecoveryReport
import Kernel.ApplicationLifecycleCompletionSource

namespace Minidregg.Kernel.ApplicationFailedStartRecoverySource

open Minidregg.Compiler
open Minidregg.Compiler.HyperdocumentCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

structure Source where
  originalBegin : ApplicationLifecycleBeginV3Ingress.Ingress
  originalClaim : ApplicationLifecycleClaimV3Ingress.Ingress
  physical : ApplicationFailedStartRecoveryReport.Signed
  currentAppRoot : Digest
  currentPackageRoot : Digest
  appCapability : CapabilityId
  appObserveCapability : CapabilityId
  packageCapability : CapabilityId
  packageObserveCapability : CapabilityId
  packageAtomBefore : Option AtomRecord
  deriving DecidableEq

def sourceStream : StreamCodec Source :=
  StreamCodec.xmap
    (StreamCodec.product ApplicationLifecycleBeginV3Ingress.ingressStream
      (StreamCodec.product ApplicationLifecycleClaimV3Ingress.ingressStream
        (StreamCodec.product ApplicationFailedStartRecoveryReport.signedStream
          (StreamCodec.product digestStream
              (StreamCodec.product digestStream
                (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
                  (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
                    (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
                      (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
                        (StreamCodec.option atomRecordStream))))))))))
    (fun source => (source.originalBegin, source.originalClaim,
      source.physical, source.currentAppRoot,
      source.currentPackageRoot, source.appCapability,
      source.appObserveCapability, source.packageCapability,
      source.packageObserveCapability, source.packageAtomBefore))
    (fun (originalBegin, originalClaim, physical,
          currentAppRoot, currentPackageRoot, appCapability,
          appObserveCapability, packageCapability, packageObserveCapability,
          packageAtomBefore) =>
      ⟨originalBegin, originalClaim, physical,
        currentAppRoot, currentPackageRoot, appCapability,
        appObserveCapability, packageCapability, packageObserveCapability,
        packageAtomBefore⟩)
    (by intro source; cases source; rfl)

def frame : List UInt8 :=
  "DREGG/APPLICATION/FAILED-START-RECOVERY-SOURCE/v1".toUTF8.toList

def codec : LawfulCodec Source := NativeHostCodec.framed frame sourceStream

def Source.canonicalBytes (source : Source) : List UInt8 := codec.encode source

def Source.app (source : Source) : Nat := source.originalBegin.base.source.app

def Source.kind (source : Source) : ApplicationLifecycleBegin.Kind :=
  source.originalBegin.base.source.kind

def Source.claimedState (source : Source) : ApplicationGrain.State :=
  (ApplicationLifecycleClaim.Kind.claimOperation source.kind).after
    source.originalClaim.base.source.before

def Source.operation (_source : Source) : ApplicationGrain.Operation :=
  .reconcileFailedStart

def Source.manifestBytes (source : Source) : List UInt8 :=
  ApplicationDispatchManifest.manifestCodec.encode
    (ApplicationLifecycleBeginV3Ingress.prospectiveManifest source.originalBegin)

def Source.packageAction (domain : Digest) (source : Source) : ContentResource.Action :=
  let atom := ApplicationDispatchManifest.manifestAtom domain source.app
  match source.packageAtomBefore with
  | none => .createAtom atom (.inlineObject ⟨13⟩) source.manifestBytes
  | some before =>
      .editAtom
        { atomId := atom
          before := before
          kind := .inlineObject ⟨13⟩
          payload := source.manifestBytes
          tombstone := false }

def Source.packageTarget (domain : Digest) (source : Source) :
    DeclaredResourceController.Target :=
  { kind := .object
    target := source.originalBegin.base.source.packageManifest
    capability := source.packageCapability
    schemaVersion := ContentResource.commandVersion
    expectedTargetRoot := source.currentPackageRoot
    payload := .content ⟨[source.packageAction domain]⟩
    observeCapability := some source.packageObserveCapability }

def Source.needsPackageWrite (_source : Source) : Bool :=
  false

def Source.valid (source : Source) : Bool :=
  decide (source.originalClaim.originalBegin = source.originalBegin ∧
    source.originalClaim.base.source.begin = source.originalBegin.base ∧
    source.physical.report.claim.core.source = source.originalClaim.base.source ∧
    source.physical.report.claim.originalClaim = source.originalClaim) &&
  source.physical.report.validFor source.originalBegin &&
  decide (source.kind = .start) &&
  (if source.kind == .install then source.packageAtomBefore.isNone
   else if source.kind == .upgrade then source.packageAtomBefore.isSome
   else true)

def Source.command (domain semantics : Digest) (source : Source) :
    DeclaredResourceController.Command :=
  let begin := source.originalBegin.base.source
  let appTarget := source.operation.target source.app source.appCapability
    source.currentAppRoot source.claimedState (some source.appObserveCapability)
  let targets := if source.needsPackageWrite then
      [appTarget, source.packageTarget domain]
    else [appTarget]
  { subject := begin.managementSubject
    nonce := (Sp800185Cshake256.hash
      "DREGG/APPLICATION/FAILED-START-RECOVERY-COMMAND/v1".toUTF8.toList
      ((StreamCodec.product digestStream
        (StreamCodec.product digestStream bytesStream)).encode
        (domain, semantics, source.physical.report.canonicalBytes))).digest.value
    targets := targets }

theorem Source.command_subject (domain semantics : Digest) (source : Source) :
    (source.command domain semantics).subject =
      source.originalBegin.base.source.managementSubject := rfl

theorem Source.command_has_app_first (domain semantics : Digest) (source : Source) :
    (source.command domain semantics).targets.head? =
      some (source.operation.target source.app source.appCapability
        source.currentAppRoot source.claimedState (some source.appObserveCapability)) := by
  simp only [Source.command, Source.needsPackageWrite]
  split <;> rfl

theorem recovery_stopped_generation (source : Source) :
    (source.operation.after source.claimedState).phase = 2 ∧
    (source.operation.after source.claimedState).generation = source.claimedState.generation + 1 ∧
    (source.operation.after source.claimedState).packageVersion = source.claimedState.packageVersion ∧
    (source.operation.after source.claimedState).snapshotVersion = source.claimedState.snapshotVersion := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end Minidregg.Kernel.ApplicationFailedStartRecoverySource
