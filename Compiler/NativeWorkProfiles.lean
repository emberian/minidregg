/-
# Compiler.NativeWorkProfiles -- Lean-owned native work and byte-codec pins

This module is the complete first-order catalog consumed by native glue
generation.  A work profile fixes its work identifier, carrier profile, request
and response byte codecs, and opaque kernel class before Rust is generated.
Rust does not choose any of these values.

The first live profile is deliberately narrow: a dot product over canonical
32-byte recursive Fan--Paar coordinates.  Its request is

```
u32_le(count) || left[count][32] || right[count][32]
```

and its response is one canonical 32-byte coordinate.  The encoder below is
Lean-owned.  Native code may implement the corresponding parser and compute,
but its reply still has no semantic authority until Lean decodes and checks it
through `Tower256NativeByteBoundary`.
-/

import Compiler.Tower256NativeByteBoundary

namespace Minidregg.Compiler.NativeWorkProfiles

open Minidregg.Theory
open Minidregg.Compiler.SemanticArtifactBundle

set_option autoImplicit false

abbrev Coordinate256 :=
  Minidregg.Compiler.Tower256NativeByteBoundary.Coordinate256

/-- Native-only ABI pin for a pair of Tower256 vectors.  It is deliberately
distinct from the semantic manifest's single-value Tower256 codec. -/
def tower256DotProductRequestCodec : ByteCodecProfile :=
  MinidreggV1Artifact.tower256DotProductRequestCodec

/-- The response reuses the semantic artifact's canonical Tower256 value-codec
identifier and value-type identifier. -/
def tower256CoordinateResponseCodec : ByteCodecProfile :=
  MinidreggV1Artifact.tower256CoordinateResponseCodec

/-- The one live native work profile.  Identifier 9101 denotes opaque Tower256
dot-product compute only; it is not a proposition or proof-system relation. -/
def tower256DotProduct : WorkProfile :=
  MinidreggV1Artifact.tower256DotProductWork

/-- The closed catalog emitted into the v1 Rust integration surface. -/
def v1Catalog : List WorkProfile :=
  MinidreggV1Artifact.nativeWorkCatalog

theorem v1Catalog_is_artifact_catalog :
    v1Catalog = MinidreggV1Artifact.bundle.nativeWorkCatalog := by
  rfl

/-! ## Exact Lean request codec -/

/-- A request whose two vectors have the same u32-representable length. -/
structure Tower256DotProductRequest where
  left : List Coordinate256
  right : List Coordinate256
  sameLength : left.length = right.length
  countFits : left.length < 2 ^ 32

/-- Four fixed little-endian base-256 digits.  `countFits` on the enclosing
request makes this an injective representation of the vector length. -/
def encodeU32LE (value : Nat) : List UInt8 :=
  (Bignum.digitsLE 256 4 value).map UInt8.ofNat

@[simp] theorem encodeU32LE_length (value : Nat) :
    (encodeU32LE value).length = 4 := by
  simp [encodeU32LE, Bignum.digitsLE_length]

/-- Exact request bytes consumed by the generated Tower256 dot-product work
constructor.  Rust receives only these bytes, never the proof fields. -/
def Tower256DotProductRequest.encode
    (request : Tower256DotProductRequest) : List UInt8 :=
  encodeU32LE request.left.length ++
    request.left.flatMap BinaryTowerFanPaarCodec.encodeFin ++
    request.right.flatMap BinaryTowerFanPaarCodec.encodeFin

theorem Tower256DotProductRequest.encode_length
    (request : Tower256DotProductRequest) :
    request.encode.length = 4 + 64 * request.left.length := by
  simp [Tower256DotProductRequest.encode, request.sameLength,
    List.length_flatMap, Nat.mul_comm]
  omega

/-- The response codec is definitionally the canonical coordinate encoder used
by the Lean semantic Tower256 boundary. -/
def encodeTower256Response (coordinate : Coordinate256) : List UInt8 :=
  BinaryTowerFanPaarCodec.encodeFin coordinate

@[simp] theorem encodeTower256Response_length (coordinate : Coordinate256) :
    (encodeTower256Response coordinate).length = 32 := by
  simp [encodeTower256Response]

theorem work_profile_exact :
    tower256DotProduct.workId = 9101 ∧
    tower256DotProduct.carrierProfileId =
      MinidreggV1Artifact.gf2Tower256Carrier.id.value ∧
    tower256DotProduct.requestCodec.codecId = 9001 ∧
    tower256DotProduct.responseCodec.codecId =
      MinidreggV1Artifact.tower256ValueCodec.codecId.value ∧
    tower256DotProduct.kernel = .tower256DotProduct := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

#print axioms Tower256DotProductRequest.encode_length
#print axioms encodeTower256Response_length
#print axioms work_profile_exact

end Minidregg.Compiler.NativeWorkProfiles
