/-
# Compiler.CredentialAuthorityReplay -- one replay key for one authority marker

The complete authority schema has one untyped nullifier map per domain.
Birth, invocation, installation and delegation therefore use this same stable
envelope for a given domain and semantic marker. Operation-specific request
identity belongs in the journaled event, not in a second consumed-key namespace.

This module is only canonical representation. It adds no replay store, no
authority interpreter and no assumption that a hash is injective.
-/
import Compiler.Tower256ConcreteBackend
import Compiler.Sp800185Cshake256
import Kernel.DurableDataIntent

namespace Minidregg.Compiler.CredentialAuthorityReplay

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

def frame : List UInt8 := "DREGG.AUTHORITY.NULLIFIER/v1".toUTF8.toList

def bytes (domain : Digest) (marker : Nat) : List UInt8 :=
  frame ++ (StreamCodec.product digestStream StreamCodec.nat).encode (domain, marker)

def nullifier (domain : Digest) (marker : Nat) : StableNullifier where
  codecVersion := 1
  domain := domain
  nullifierId := ⟨marker⟩
  canonicalBytes := bytes domain marker

/-- Equality follows the actual domain and semantic map key, independently
of the operation that consumes it or the descriptor being retried. -/
theorem nullifier_eq_iff (leftDomain rightDomain : Digest) (left right : Nat) :
    nullifier leftDomain left = nullifier rightDomain right ↔
      leftDomain = rightDomain ∧ left = right := by
  constructor
  · intro same
    exact ⟨congrArg StableNullifier.domain same,
      congrArg (fun value : StableNullifier => value.nullifierId.value) same⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The exact bytes retain both coordinates even independently of the other
stable-envelope fields. This is codec injectivity, never hash reflection. -/
theorem bytes_injective (leftDomain rightDomain : Digest) (left right : Nat)
    (same : bytes leftDomain left = bytes rightDomain right) :
    leftDomain = rightDomain ∧ left = right := by
  have encoded : (StreamCodec.product digestStream StreamCodec.nat).encode (leftDomain, left) =
      (StreamCodec.product digestStream StreamCodec.nat).encode (rightDomain, right) :=
    List.append_cancel_left same
  let codec := (StreamCodec.product digestStream StreamCodec.nat).toLawful
  have encoded' : codec.encode (leftDomain, left) = codec.encode (rightDomain, right) := encoded
  have decoded := congrArg codec.decode encoded'
  simp only [codec.decode_encode, Option.some.injEq, Prod.mk.injEq] at decoded
  exact decoded

/-! ## Source-owned birth identity, before any payload or root is chosen -/

def birthIdentityFrame : List UInt8 :=
  "DREGG/RESOURCE-BIRTH/IDENTITY".toUTF8.toList ++ [1]

def birthIdentityCustomization : List UInt8 :=
  "DREGG.RESOURCE.BIRTH.IDENTITY/v1".toUTF8.toList

def birthIdentityStream : StreamCodec (Digest × (Digest × (Nat × (Nat × Nat)))) :=
  StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat StreamCodec.nat)))

/-- The operation family, deployment, compatible runtime, actual factory,
signed creator and nonce own this coordinate. Payloads and roots are excluded
so changing them under one coordinate remains a transaction conflict. -/
def birthIdentityBytes (domain semantics : Digest) (factory : ResourceId .object)
    (creator : SubjectId) (nonce : Nat) : List UInt8 :=
  birthIdentityFrame ++ birthIdentityStream.encode
    (domain, semantics, factory.value, creator.value, nonce)

def birthIdentity (domain semantics : Digest) (factory : ResourceId .object)
    (creator : SubjectId) (nonce : Nat) : Digest :=
  (Sp800185Cshake256.hash birthIdentityCustomization
    (birthIdentityBytes domain semantics factory creator nonce)).digest

/-- The unhashed canonical coordinate retains every scope field. This is a
codec theorem; it deliberately does not assert that the digest is injective. -/
theorem birthIdentityBytes_injective
    (leftDomain rightDomain leftSemantics rightSemantics : Digest)
    (leftFactory rightFactory : ResourceId .object) (leftCreator rightCreator : SubjectId)
    (leftNonce rightNonce : Nat)
    (same : birthIdentityBytes leftDomain leftSemantics leftFactory leftCreator leftNonce =
      birthIdentityBytes rightDomain rightSemantics rightFactory rightCreator rightNonce) :
    leftDomain = rightDomain ∧ leftSemantics = rightSemantics ∧
      leftFactory = rightFactory ∧ leftCreator = rightCreator ∧ leftNonce = rightNonce := by
  have encoded : birthIdentityStream.encode
      (leftDomain, leftSemantics, leftFactory.value, leftCreator.value, leftNonce) =
      birthIdentityStream.encode
        (rightDomain, rightSemantics, rightFactory.value, rightCreator.value, rightNonce) :=
    List.append_cancel_left same
  have decoded := congrArg birthIdentityStream.toLawful.decode encoded
  have leftDecoded := birthIdentityStream.toLawful.decode_encode
    (leftDomain, leftSemantics, leftFactory.value, leftCreator.value, leftNonce)
  have rightDecoded := birthIdentityStream.toLawful.decode_encode
    (rightDomain, rightSemantics, rightFactory.value, rightCreator.value, rightNonce)
  change birthIdentityStream.toLawful.decode (birthIdentityStream.encode _) = some _ at leftDecoded
  change birthIdentityStream.toLawful.decode (birthIdentityStream.encode _) = some _ at rightDecoded
  rw [leftDecoded, rightDecoded] at decoded
  have coordinates := Option.some.inj decoded
  have domains := congrArg Prod.fst coordinates
  have semantics := congrArg (fun value => value.2.1) coordinates
  have factories := congrArg (fun value => value.2.2.1) coordinates
  have creators := congrArg (fun value => value.2.2.2.1) coordinates
  have nonces := congrArg (fun value => value.2.2.2.2) coordinates
  cases leftFactory; cases rightFactory; cases leftCreator; cases rightCreator
  exact ⟨domains, semantics, by cases factories; rfl, by cases creators; rfl, nonces⟩

end Minidregg.Compiler.CredentialAuthorityReplay
