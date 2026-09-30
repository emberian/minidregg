/-
Native checking for an owner-signed selective release. This is an admission
ingredient, not an installed Mini effect or a source-history receipt. The
recipient selects the current key and current policy source from its complete
opened authority; no fn article or caller-supplied verifier bit selects them.
-/
import Kernel.FnSelectiveRelease
import Kernel.FnGatewayPolicy
import Compiler.CredentialSignatureAdmission

namespace Minidregg.Kernel.FnSelectiveReleaseSignature

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialSigningKey
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.FnSelectiveRelease

set_option autoImplicit false

/-- The signature is detached from the exact canonical release preimage.
The packet codec is intentionally separate from the existing full-history
FnEvidence codec. -/
structure Packet where
  release : Release
  signature : List UInt8
  deriving DecidableEq, Repr

def packetStream : StreamCodec Packet :=
  StreamCodec.xmap
    (StreamCodec.product releaseStream Tower256ConcreteBackend.bytesStream)
    (fun packet => (packet.release, packet.signature))
    (fun wire => ⟨wire.1, wire.2⟩)
    (by intro packet; cases packet; rfl)

def packetCodec : LawfulCodec Packet :=
  ResourceBirthCodec.strictCodec
    (NativeHostCodec.framed "DREGG/FN/SELECTIVE-OWNER-PACKET/v2".toUTF8.toList packetStream)

theorem packetCodec_accepted_bytes {bytes : List UInt8} {packet : Packet}
    (accepted : packetCodec.decode bytes = some packet) :
    packetCodec.encode packet = bytes := by
  unfold packetCodec at accepted ⊢
  exact ResourceBirthCodec.strictCodec_canonical
    (NativeHostCodec.framed "DREGG/FN/SELECTIVE-OWNER-PACKET/v2".toUTF8.toList packetStream)
    accepted

/-- Source and destination fields remain signed context, not evidence of
source admission. The current recipient law is deliberately the exact
owner-subject lock. This prevents a gateway credential from exercising the
ordinary DRC mutate path on the same target. -/
structure Selected (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (release : Release) where
  destination : release.destination.domain = config.deployment.domain ∧
    release.destination.semantics = config.profile.semantics
  bounded : release.bounded = true
  unexpired : NativeHost.logicalHeight config opened.durable ≤ release.owner.expiresAt
  key : KeyRecord
  currentKey : CredentialAuthorityState.currentSigningKey
    opened.authority.snapshot.logical ⟨release.owner.subject⟩ = some key
  keyEpoch : key.keyEpoch = release.owner.epoch
  algorithm : key.algorithm = CredentialSignatureAdmission.ed25519Algorithm
  publicKeyLength : key.publicKey.length = 32
  active : key.revoked = false ∧
    key.activeFrom ≤ opened.authority.snapshot.revision ∧
    opened.authority.snapshot.revision ≤ key.activeUntil
  policyHeadValue : Minidregg.Theory.PolicyInstall.Head
  policyHead : CredentialAuthorityDomain.headAt
    opened.authority.snapshot.logical ⟨release.destination.target⟩ =
    some policyHeadValue
  law : CanonicalCellRegistry.LoadedPolicySource config.deployment.domain
    opened.directory.directory policyHeadValue.address
  lawAddress : policyHeadValue.address = release.owner.policyRoot
  audienceLaw : law.record.policyId = ⟨release.destination.target⟩ ∧
    law.record.version = policyHeadValue.version ∧
    law.record.semantics = config.profile.semantics ∧
    release.destination.audience.policyRoot = policyHeadValue.address
  subjectLaw : FnGatewayPolicy.subjectLocked ⟨release.owner.subject⟩ law.record.predicate = true

inductive Reject where
  | wrongDestination
  | confidentialProfileUnavailable
  | unbounded
  | expired
  | missingCurrentKey
  | wrongKeyEpoch
  | unsupportedAlgorithm
  | inactiveKey
  | noCurrentPolicy
  | policyMismatch
  | missingPolicySource
  | ownerLawMismatch
  | signatureLength
  | signatureInvalid
  | native (reason : CredentialSignatureIO.Error)
  deriving DecidableEq, Repr

def select (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (release : Release) : Except Reject (Selected config opened release) := do
  if release.destination.audience.visibility != .publicPeerable then
    throw .confidentialProfileUnavailable
  if destination : release.destination.domain = config.deployment.domain ∧
      release.destination.semantics = config.profile.semantics then
    if bounded : release.bounded = true then
      if unexpired : NativeHost.logicalHeight config opened.durable ≤ release.owner.expiresAt then
        match currentKey : CredentialAuthorityState.currentSigningKey
            opened.authority.snapshot.logical ⟨release.owner.subject⟩ with
        | none => .error .missingCurrentKey
        | some key =>
            if keyEpoch : key.keyEpoch = release.owner.epoch then
              if algorithm : key.algorithm = CredentialSignatureAdmission.ed25519Algorithm ∧
                  key.publicKey.length = 32 then
                if active : key.revoked = false ∧
                    key.activeFrom ≤ opened.authority.snapshot.revision ∧
                    opened.authority.snapshot.revision ≤ key.activeUntil then
                  match policyHead : CredentialAuthorityDomain.headAt
                      opened.authority.snapshot.logical ⟨release.destination.target⟩ with
                  | none => .error .noCurrentPolicy
                  | some head =>
                      match CanonicalCellRegistry.loadPolicySource config.deployment.domain
                          opened.directory.directory head.address with
                      | none => .error .missingPolicySource
                      | some law =>
                          if lawAddress : head.address = release.owner.policyRoot then
                            if audienceLaw : law.record.policyId = ⟨release.destination.target⟩ ∧
                                law.record.version = head.version ∧
                                law.record.semantics = config.profile.semantics ∧
                                release.destination.audience.policyRoot = head.address then
                              if subjectLaw : FnGatewayPolicy.subjectLocked
                                  ⟨release.owner.subject⟩ law.record.predicate = true then
                                .ok ⟨destination, bounded, unexpired,
                                  key, currentKey, keyEpoch, algorithm.1,
                                  algorithm.2, active, head, policyHead, law,
                                  lawAddress, audienceLaw, subjectLaw⟩
                              else .error .ownerLawMismatch
                            else .error .policyMismatch
                          else .error .policyMismatch
                else .error .inactiveKey
              else .error .unsupportedAlgorithm
            else .error .wrongKeyEpoch
      else .error .expired
    else .error .unbounded
  else .error .wrongDestination

/-- Only this IO function can mint a checked owner packet. It binds the
verified exact preimage, selected current key, current policy source, and
the physical verifier configuration. No successful `Bool` is accepted from
the caller. This still has no durable receiving effect by itself. -/
structure Checked (config : NativeHost.Config) (opened : NativeHost.Opened config) where
  private mk ::
  packet : Packet
  selection : Selected config opened packet.release
  selected : select config opened packet.release = .ok selection
  verifier : CredentialSignatureIO.NativeConfig
  signatureLength : packet.signature.length = 64

def verifyNative (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (packet : Packet) : IO (Except Reject (Checked config opened)) := do
  match selected : select config opened packet.release with
  | .error reason => return .error reason
  | .ok selection =>
      if signatureLength : packet.signature.length = 64 then
        let checked ← CredentialSignatureIO.verify config.signature selection.key.publicKey
            (signedPreimage packet.release) packet.signature
        match checked with
        | .error reason => return .error (.native reason)
        | .ok false => return .error .signatureInvalid
        | .ok true =>
            return .ok ⟨packet, selection, selected, config.signature, signatureLength⟩
      else return .error .signatureLength

/-- The committed current law for a checked owner packet excludes an ordinary
gateway subject with a different identity at this recipient. This does not
itself admit the special release command; native receiving must enforce its
separate ingress and replay marker. -/
theorem ordinary_gateway_refused (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (checked : Checked config opened)
    (gateway : SubjectId) (old new : Minidregg.Pred.State)
    (projected : new.get "request/subject" = some (Int.ofNat gateway.value))
    (different : gateway ≠ ⟨checked.packet.release.owner.subject⟩) :
    Minidregg.Pred.eval checked.selection.law.record.predicate old new = false :=
  FnGatewayPolicy.non_gateway_subject_refused
    ⟨checked.packet.release.owner.subject⟩ gateway
    checked.selection.law.record.predicate old new
    checked.selection.subjectLaw projected different

end Minidregg.Kernel.FnSelectiveReleaseSignature
