/-
Canonical, source-authored identity for an application lifecycle BEGIN. The
ordinary DRC command supplies current mutation authority; this carrier binds
the physical work requested of a later host to that signed command. It does
not grant a completion slot or permission to launch a process.
-/
import Kernel.ApplicationGrain
import Kernel.DurableDataIntent
import Compiler.ResourceBirthCodec

namespace Minidregg.Kernel.ApplicationLifecycleBegin

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.DeclaredEffectPageMaterializer
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

inductive Kind where
  | install | start | stop | upgrade
  deriving DecidableEq, Repr

def Kind.code : Kind → Nat
  | .install => 0 | .start => 1 | .stop => 2 | .upgrade => 3

def Kind.ofCode : Nat → Kind
  | 0 => .install | 1 => .start | 2 => .stop | _ => .upgrade

def kindStream : StreamCodec Kind :=
  StreamCodec.xmap StreamCodec.nat Kind.code Kind.ofCode
    (by intro kind; cases kind <;> rfl)

def Kind.operation : Kind → ApplicationGrain.Operation
  | .install => .beginInstall
  | .start => .beginStart
  | .stop => .beginStop
  | .upgrade => .beginUpgrade

def Kind.requiredPhase : Kind → Int
  | .install => 0
  | .start => 2
  | .stop => 4
  | .upgrade => 2

def stateStream : StreamCodec ApplicationGrain.State :=
  StreamCodec.xmap
    (StreamCodec.product intStream
      (StreamCodec.product intStream (StreamCodec.product intStream intStream)))
    (fun s => (s.generation, s.phase, s.packageVersion, s.snapshotVersion))
    (fun (generation, phase, packageVersion, snapshotVersion) =>
      ⟨generation, phase, packageVersion, snapshotVersion⟩)
    (by intro s; cases s; rfl)

/-- `imageIdentity` names the intended immutable materialization, while
`processIdentity` names the intended host unit/cgroup generation. Neither is
a claim that the physical operation has happened. The host attestation will
have to compare both to its observed effect. -/
structure Source where
  kind : Kind
  app : Nat
  packageManifest : Nat
  snapshotManifest : Nat
  operationId : Nat
  subject : SubjectId
  managementSubject : SubjectId
  capability : CapabilityId
  packageObserveCapability : CapabilityId
  before : ApplicationGrain.State
  authorityRoot : Digest
  appRoot : Digest
  packageRoot : Digest
  packageDigest : Digest
  imageIdentity : List UInt8
  processGeneration : Int
  processIdentity : List UInt8
  deriving DecidableEq, Repr

def Source.valid (source : Source) : Bool :=
  decide (source.app ≠ source.packageManifest ∧
    source.app ≠ source.snapshotManifest ∧
    source.packageManifest ≠ source.snapshotManifest ∧
    source.before.phase = source.kind.requiredPhase ∧
    source.processGeneration = source.before.generation + 1 ∧
    0 ≤ source.before.generation ∧ 0 ≤ source.before.packageVersion ∧
    0 ≤ source.before.snapshotVersion) &&
  !source.imageIdentity.isEmpty && source.imageIdentity.length ≤ 256 &&
  !source.processIdentity.isEmpty && source.processIdentity.length ≤ 256

theorem Source.valid_distinct (source : Source) (valid : source.valid = true) :
    source.app ≠ source.packageManifest ∧
    source.app ≠ source.snapshotManifest ∧
    source.packageManifest ≠ source.snapshotManifest := by
  simp only [Source.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
  aesop

theorem Source.empty_image_refused (source : Source)
    (empty : source.imageIdentity = []) : source.valid = false := by
  simp [Source.valid, empty]

theorem Source.empty_process_refused (source : Source)
    (empty : source.processIdentity = []) : source.valid = false := by
  simp [Source.valid, empty]

def sourceStream : StreamCodec Source :=
  StreamCodec.xmap
    (StreamCodec.product kindStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product StreamCodec.nat
            (StreamCodec.product StreamCodec.nat
            (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
              (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
              (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
                (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
                  (StreamCodec.product stateStream
                    (StreamCodec.product digestStream
                    (StreamCodec.product digestStream
                    (StreamCodec.product digestStream
                      (StreamCodec.product digestStream
                        (StreamCodec.product bytesStream
                          (StreamCodec.product intStream bytesStream))))))))))))))))
    (fun s => (s.kind, s.app, s.packageManifest, s.snapshotManifest,
      s.operationId, s.subject, s.managementSubject, s.capability,
      s.packageObserveCapability, s.before,
      s.authorityRoot, s.appRoot, s.packageRoot,
      s.packageDigest, s.imageIdentity, s.processGeneration, s.processIdentity))
    (fun (kind, app, packageManifest, snapshotManifest, operationId, subject,
          managementSubject, capability,
          packageObserveCapability, before, authorityRoot, appRoot, packageRoot,
          packageDigest, imageIdentity, processGeneration, processIdentity) =>
      ⟨kind, app, packageManifest, snapshotManifest, operationId, subject,
        managementSubject, capability,
        packageObserveCapability, before, authorityRoot, appRoot, packageRoot,
        packageDigest, imageIdentity, processGeneration, processIdentity⟩)
    (by intro s; cases s; rfl)

private def frame : List UInt8 :=
  "DREGG/APPLICATION/LIFECYCLE-BEGIN/v1".toUTF8.toList

private def rawSourceCodec : LawfulCodec Source where
  encode source := frame ++ sourceStream.encode source
  decode bytes := if bytes.take frame.length = frame then
    sourceStream.toLawful.decode (bytes.drop frame.length) else none
  decode_encode := by
    intro source
    have decoded := sourceStream.toLawful.decode_encode source
    change sourceStream.toLawful.decode (sourceStream.encode source) = some source at decoded
    simp [decoded]

def sourceCodec : LawfulCodec Source := strictCodec rawSourceCodec

def Source.canonicalBytes (source : Source) : List UInt8 :=
  sourceCodec.encode source

theorem source_decode_encode (source : Source) :
    sourceCodec.decode source.canonicalBytes = some source :=
  sourceCodec.decode_encode source

theorem source_decoded_canonical {bytes : List UInt8} {source : Source}
    (decoded : sourceCodec.decode bytes = some source) :
    source.canonicalBytes = bytes :=
  strictCodec_canonical rawSourceCodec decoded

/-- The operation key stays stable when a different proposed image or package
is presented under the same app generation and caller operation ID. -/
abbrev Key := Digest × Digest × Nat × Int × Nat

def keyStream : StreamCodec Key :=
  StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product StreamCodec.nat (StreamCodec.product intStream StreamCodec.nat)))

def key (domain semantics : Digest) (source : Source) : Key :=
  (domain, semantics, source.app, source.before.generation + 1, source.operationId)

def keyBytes (domain semantics : Digest) (source : Source) : List UInt8 :=
  keyStream.encode (key domain semantics source)

theorem keyBytes_eq_iff_key (domain semantics : Digest) (left right : Source) :
    keyBytes domain semantics left = keyBytes domain semantics right ↔
      key domain semantics left = key domain semantics right :=
  (lawful_encode_injective keyStream.toLawful).eq_iff

def sourceDigest (domain semantics : Digest) (source : Source) : Digest :=
  (Sp800185Cshake256.hash "DREGG/APPLICATION/LIFECYCLE-BEGIN-SOURCE/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream)).encode
      (domain, semantics, source.canonicalBytes))).digest

/-- The signed DRC nonce commits to every source field. Its equality to an
actual signed command is checked by admission; hash collision resistance is
a deployment premise, not a Lean injectivity theorem. -/
def nonce (domain semantics : Digest) (source : Source) : Nat :=
  (sourceDigest domain semantics source).value

def command (domain semantics : Digest) (source : Source) :
    DeclaredResourceController.Command :=
  ApplicationGrain.Operation.command source.kind.operation source.subject
    source.authorityRoot (nonce domain semantics source) source.app source.capability
    source.appRoot source.before

def stableNullifier (domain semantics : Digest) (source : Source) : StableNullifier where
  codecVersion := 12
  domain := domain
  nullifierId := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/LIFECYCLE-BEGIN-KEY/v1".toUTF8.toList
    (keyBytes domain semantics source)).digest
  canonicalBytes := "DREGG/APPLICATION/LIFECYCLE-BEGIN-NULLIFIER/v1".toUTF8.toList ++
    keyBytes domain semantics source

theorem stableNullifier_same_key (domain semantics : Digest) (left right : Source)
    (same : key domain semantics left = key domain semantics right) :
    stableNullifier domain semantics left = stableNullifier domain semantics right := by
  simp [stableNullifier, keyBytes, same]

end Minidregg.Kernel.ApplicationLifecycleBegin
