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

end Minidregg.Compiler.CredentialAuthorityReplay
