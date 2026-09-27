/-
Canonical receiving ingress for an owner-signed selected release. The unsigned
capability and expected-root fields only select current recipient witnesses;
the owner-signed packet determines all effect bytes, target and nonce. Fresh
admission must verify the capability, owner key and current law before this
derived command may become a durable intent. The distinct event is essential:
an ordinary DRC mutation of similar content is not a checked release.
-/
import Kernel.FnSelectiveReleaseSignature
import Kernel.DeclaredResourceController

namespace Minidregg.Kernel.FnSelectiveReleaseIngress

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.IndexedProgram
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.FnSelectiveRelease
open Minidregg.Kernel.FnSelectiveReleaseSignature

set_option autoImplicit false

structure Ingress where
  packet : Packet
  capability : CapabilityId
  expectedAuthorityRoot : Digest
  expectedTargetRoot : Digest
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap
    (StreamCodec.product packetStream
      (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
        (StreamCodec.product digestStream digestStream)))
    (fun ingress => (ingress.packet, ingress.capability,
      ingress.expectedAuthorityRoot, ingress.expectedTargetRoot))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2⟩)
    (by intro ingress; cases ingress; rfl)

def ingressCodec : LawfulCodec Ingress :=
  ResourceBirthCodec.strictCodec
    (NativeHostCodec.framed "DREGG/FN/SELECTIVE-INGRESS/v2".toUTF8.toList ingressStream)

theorem ingressCodec_accepted_bytes {bytes : List UInt8} {ingress : Ingress}
    (accepted : ingressCodec.decode bytes = some ingress) :
    ingressCodec.encode ingress = bytes := by
  unfold ingressCodec at accepted ⊢
  exact ResourceBirthCodec.strictCodec_canonical
    (NativeHostCodec.framed "DREGG/FN/SELECTIVE-INGRESS/v2".toUTF8.toList ingressStream)
    accepted

/-- The release key excludes gateway witness choice and owner subject. It is
the same recipient-domain/target/nonce namespace across all attempted
signatures and all fn articles, modulo the stated cSHAKE collision boundary. -/
def keyBytes (release : Release) : List UInt8 :=
  (StreamCodec.product digestStream
    (StreamCodec.product StreamCodec.nat digestStream)).encode
    (release.destination.domain, release.destination.target, release.owner.nonce)

def keyDigest (release : Release) : Digest :=
  (Sp800185Cshake256.hash "DREGG/FN/SELECTIVE-RELEASE-KEY/v2".toUTF8.toList
    (keyBytes release)).digest

def releaseNullifier (release : Release) : StableNullifier where
  codecVersion := 13
  domain := release.destination.domain
  nullifierId := keyDigest release
  canonicalBytes := "DREGG/FN/SELECTIVE-RELEASE-NULLIFIER/v2".toUTF8.toList ++
    keyBytes release

def atomId (release : Release) : AtomId :=
  ⟨⟨(keyDigest release).value⟩⟩

/-- Every effect byte is a pure function of the owner-signed Packet. The
unsigned outer fields are only current witness selectors. -/
def command (ingress : Ingress) : DeclaredResourceController.Command :=
  let release := ingress.packet.release
  { subject := ⟨release.owner.subject⟩
    expectedAuthorityRoot := ingress.expectedAuthorityRoot
    nonce := (keyDigest release).value
    targets :=
      [{ kind := .object
         target := release.destination.target
         capability := ingress.capability
         schemaVersion := ContentResource.commandVersion
         expectedTargetRoot := ingress.expectedTargetRoot
         payload := .content ⟨[.createAtom (atomId release)
           (.inlineObject ⟨11⟩) (packetCodec.encode ingress.packet)]⟩ }] }

theorem command_subject_exact (ingress : Ingress) :
    (command ingress).subject = ⟨ingress.packet.release.owner.subject⟩ := rfl

theorem command_target_exact (ingress : Ingress) :
    ((command ingress).targets.head?).map DeclaredResourceController.Target.target =
      some ingress.packet.release.destination.target := rfl

theorem command_payload_exact (ingress : Ingress) :
    ((command ingress).targets.head?).map DeclaredResourceController.Target.payload =
      some (DeclaredResourceController.Payload.content ⟨[.createAtom (atomId ingress.packet.release)
        (.inlineObject ⟨11⟩) (packetCodec.encode ingress.packet)]⟩) := rfl

def transactionId (ingress : Ingress) : Digest := keyDigest ingress.packet.release

def event (ingress : Ingress) : StableEvent where
  codecVersion := 13
  domain := ingress.packet.release.destination.domain
  eventId := (Sp800185Cshake256.hash
    "DREGG/FN/SELECTIVE-RELEASE-EVENT/v2".toUTF8.toList
    (ingressCodec.encode ingress)).digest
  canonicalBytes := ingressCodec.encode ingress

theorem event_exact (ingress : Ingress) :
    (event ingress).canonicalBytes = ingressCodec.encode ingress := rfl

/-- The special release marker is provably distinct from the ordinary DRC
marker even if their digest values collide: the codec version is different. -/
theorem releaseNullifier_ne_ordinary (release : Release) (marker : Nat) :
    releaseNullifier release ≠ CredentialAuthorityReplay.nullifier
      release.destination.domain marker := by
  intro same
  have version : (13 : Nat) = 1 := congrArg StableNullifier.codecVersion same
  omega

end Minidregg.Kernel.FnSelectiveReleaseIngress
