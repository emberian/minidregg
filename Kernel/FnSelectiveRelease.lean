/-
A distinct, resource-owned release message for selected private content. Its
canonical bytes are suitable for an actual native signature check and a
governed receiving command. Nothing in this module treats a claimed source
receipt, an fn article, or a caller-supplied signature result as authority.
The receiving integration must bind a verified signer and current local law
to this exact message before it installs any effect.
-/
import Compiler.FnEvidenceCodec

namespace Minidregg.Kernel.FnSelectiveRelease

open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

/-- Source coordinates are context, not a proof that an operation was accepted
there. The parent digest binds the selected resource context the owner meant
to disclose. -/
structure SourceRef where
  domain : Digest
  semantics : Digest
  resource : Nat
  parent : Digest
  deriving DecidableEq, Repr

inductive Visibility where
  | recipientOnly
  | publicPeerable
  deriving DecidableEq, Repr

/-- Audience intent is signed independently of the fn routing group. A
newsgroup is not access control, and `recipientOnly` does not encrypt content
or make an fn article confidential. A later encrypted publication profile
must bind its ciphertext, plaintext commitment and format separately. -/
structure Audience where
  visibility : Visibility
  policyRoot : Digest
  keysetRoot : Digest
  epoch : Nat
  deriving DecidableEq, Repr

structure Destination where
  domain : Digest
  semantics : Digest
  target : Nat
  group : List UInt8
  messageId : List UInt8
  audience : Audience
  deriving DecidableEq, Repr

/-- The receiver independently pins the policy root and verifies the signer.
The epoch and expiry are signed coordinates, not proof of source freshness. -/
structure OwnerScope where
  policyRoot : Digest
  subject : Nat
  epoch : Nat
  nonce : Digest
  expiresAt : Nat
  deriving DecidableEq, Repr

structure Release where
  source : SourceRef
  destination : Destination
  owner : OwnerScope
  content : List UInt8
  deriving DecidableEq, Repr

def sourceRefStream : StreamCodec SourceRef :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product StreamCodec.nat digestStream)))
    (fun value => (value.domain, value.semantics, value.resource, value.parent))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2⟩)
    (by intro value; cases value; rfl)

def visibilityStream : StreamCodec Visibility :=
  StreamCodec.xmap StreamCodec.bool
    (fun value => match value with
      | .recipientOnly => false
      | .publicPeerable => true)
    (fun value => if value then .publicPeerable else .recipientOnly)
    (by intro value; cases value <;> rfl)

def audienceStream : StreamCodec Audience :=
  StreamCodec.xmap
    (StreamCodec.product visibilityStream
      (StreamCodec.product digestStream
        (StreamCodec.product digestStream StreamCodec.nat)))
    (fun value => (value.visibility, value.policyRoot,
      value.keysetRoot, value.epoch))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2⟩)
    (by intro value; cases value; rfl)

def destinationStream : StreamCodec Destination :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product bytesStream
            (StreamCodec.product bytesStream audienceStream)))))
    (fun value => (value.domain, value.semantics, value.target,
      value.group, value.messageId, value.audience))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1,
      wire.2.2.2.1, wire.2.2.2.2.1, wire.2.2.2.2.2⟩)
    (by intro value; cases value; rfl)

def ownerScopeStream : StreamCodec OwnerScope :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product digestStream StreamCodec.nat))))
    (fun value => (value.policyRoot, value.subject, value.epoch,
      value.nonce, value.expiresAt))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1,
      wire.2.2.2.1, wire.2.2.2.2⟩)
    (by intro value; cases value; rfl)

def releaseStream : StreamCodec Release :=
  StreamCodec.xmap
    (StreamCodec.product sourceRefStream
      (StreamCodec.product destinationStream
        (StreamCodec.product ownerScopeStream bytesStream)))
    (fun value => (value.source, value.destination, value.owner, value.content))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2⟩)
    (by intro value; cases value; rfl)

/-- This is a new inner profile. Existing native-prefix packages and fn
carriers retain their own codecs and meanings. -/
def releaseCodec : LawfulCodec Release :=
  NativeHostCodec.framed "DREGG/FN/SELECTIVE-RELEASE/v1".toUTF8.toList releaseStream

/-- The entire released content and every scope coordinate enter the message
that a native signature verifier must check. No digest collision assumption is
needed to establish byte-level injectivity of this canonical encoding. -/
def signedPreimage (release : Release) : List UInt8 := releaseCodec.encode release

theorem signedPreimage_injective : Function.Injective signedPreimage := by
  intro left right same
  have decoded := congrArg releaseCodec.decode same
  exact Option.some.inj (by
    simpa only [signedPreimage, releaseCodec.decode_encode] using decoded)

/-- Allocation ceiling for the selected transport profile. This is not
authorization or a statement that a particular fn Store admits the article. -/
def Release.bounded (release : Release) : Bool :=
  !release.content.isEmpty &&
  release.content.length ≤ FnEvidenceCodec.maxCarrierBytes &&
  !release.destination.group.isEmpty && release.destination.group.length ≤ 256 &&
  !release.destination.messageId.isEmpty &&
    release.destination.messageId.length ≤ 256 &&
  (signedPreimage release).length ≤ FnEvidenceCodec.maxCarrierBytes + 4096

/-- One-use key at the receiving resource. The nonce namespace cannot be
reset merely by changing the claimed source or owner epoch. -/
structure Key where
  receiverDomain : Digest
  receiverTarget : Nat
  nonce : Digest
  deriving DecidableEq, Repr

def Release.key (release : Release) : Key :=
  ⟨release.destination.domain, release.destination.target, release.owner.nonce⟩

structure Recorded where
  release : Release
  signedCall : List UInt8
  deriving DecidableEq, Repr

inductive PriorDecision where
  | unrelated
  | exactRepeat
  | conflict
  deriving DecidableEq, Repr

/-- A matching nonce only repeats with the same complete release *and* the
same signed native call. A new signature or changed bytes must not be
misreported as recovery of the old receipt. The receiving journal remains
the authority for whether this record actually exists. -/
def comparePrior (prior : Recorded) (incoming : Release)
    (signedCall : List UInt8) : PriorDecision :=
  if prior.release.key == incoming.key then
    if prior.release == incoming && prior.signedCall == signedCall then
      .exactRepeat
    else .conflict
  else .unrelated

theorem comparePrior_exactRepeat (prior : Recorded) (incoming : Release)
    (signedCall : List UInt8)
    (same : comparePrior prior incoming signedCall = .exactRepeat) :
    prior.release = incoming ∧ prior.signedCall = signedCall := by
  by_cases sameKey : prior.release.key = incoming.key
  · by_cases sameRelease : prior.release = incoming
    · by_cases sameCall : prior.signedCall = signedCall
      · exact ⟨sameRelease, sameCall⟩
      · simp [comparePrior, sameRelease, sameCall] at same
    · simp [comparePrior, sameKey, sameRelease] at same
  · simp [comparePrior, sameKey] at same

theorem comparePrior_conflict (prior : Recorded) (incoming : Release)
    (signedCall : List UInt8)
    (sameKey : prior.release.key = incoming.key)
    (changed : prior.release ≠ incoming ∨ prior.signedCall ≠ signedCall) :
    comparePrior prior incoming signedCall = .conflict := by
  by_cases sameRelease : prior.release = incoming
  · by_cases sameCall : prior.signedCall = signedCall
    · exact False.elim (changed.elim
        (fun notRelease => notRelease sameRelease)
        (fun notCall => notCall sameCall))
    · simp [comparePrior, sameRelease, sameCall]
  · simp [comparePrior, sameKey, sameRelease]

end Minidregg.Kernel.FnSelectiveRelease
