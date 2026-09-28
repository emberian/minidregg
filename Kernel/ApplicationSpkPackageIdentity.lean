/-
Source-owned identity for an actual signature-verified Sandstorm SPK image.
The physical host must derive every field from the same bounded, verified
package parse before it accepts a lifecycle install/claim. A naked SHA-256
decimal value or caller-asserted interface schema is not a package identity.
The v1 descriptor has no optional or alternative layouts. The v2 API profile
uses the same field stream with a separate canonical frame and root domain.
-/
import Kernel.ApplicationDispatchManifest
import Compiler.NativeHostCodec

namespace Minidregg.Kernel.ApplicationSpkPackageIdentity

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram

set_option autoImplicit false

/-- `rawSha256`, `manifestSha256` and `bridgeConfigSha256` are raw 32-byte
SHA-256 outputs in their ordinary byte order, not decimal Digest values.
`signedAppId` comes from the SPK signing public key, not a manifest assertion.
`interfaces` is an ordered Mini interface mapping: the ordered permission and
role schema comes from signed bridge ViewInfo/config, while Mini interface
IDs, versions and web/API kinds follow a separately checked source-owned
mapping rule. The signed SPK does not itself choose those Mini coordinates. -/
structure Descriptor where
  rawSha256 : List UInt8
  rawLength : Nat
  signedAppId : List UInt8
  signedAppVersion : Nat
  manifestSha256 : List UInt8
  bridgeConfigSha256 : List UInt8
  bridgeApiPath : List UInt8
  interfaces : List ApplicationDispatchManifest.Interface
  deriving DecidableEq, Repr

def descriptorStream : StreamCodec Descriptor :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product bytesStream
          (StreamCodec.product StreamCodec.nat
            (StreamCodec.product bytesStream
              (StreamCodec.product bytesStream
                (StreamCodec.product bytesStream
                  (StreamCodec.list ApplicationDispatchManifest.interfaceStream))))))))
    (fun descriptor => (descriptor.rawSha256, descriptor.rawLength,
      descriptor.signedAppId, descriptor.signedAppVersion,
      descriptor.manifestSha256, descriptor.bridgeConfigSha256,
      descriptor.bridgeApiPath, descriptor.interfaces))
    (fun (rawSha256, rawLength, signedAppId, signedAppVersion,
          manifestSha256, bridgeConfigSha256, bridgeApiPath, interfaces) =>
      ⟨rawSha256, rawLength, signedAppId, signedAppVersion,
        manifestSha256, bridgeConfigSha256, bridgeApiPath, interfaces⟩)
    (by intro descriptor; cases descriptor; rfl)

def codec : LawfulCodec Descriptor :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/SPK-PACKAGE-IDENTITY/v1".toUTF8.toList descriptorStream

def codecV2 : LawfulCodec Descriptor :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/SPK-PACKAGE-IDENTITY/v2".toUTF8.toList descriptorStream

/-- Legacy GitWeb and web-only descriptors retain their v1 identity. Every
other admitted API prefix has an explicit v2 identity. This choice depends
only on the signed path, so nested descriptor streams retain the profile. -/
def Descriptor.legacyProfile (descriptor : Descriptor) : Bool :=
  descriptor.bridgeApiPath.isEmpty ||
    descriptor.bridgeApiPath == "/repo.git/".toUTF8.toList

def Descriptor.canonicalBytes (descriptor : Descriptor) : List UInt8 :=
  if descriptor.legacyProfile then codec.encode descriptor
  else codecV2.encode descriptor

/-- A framed v1 identity for a new API path, or a v2 re-encoding of a legacy
identity, is never a second spelling of the same admitted descriptor. -/
def decodeCanonical (bytes : List UInt8) : Option Descriptor :=
  match codec.decode bytes with
  | some descriptor =>
      if descriptor.legacyProfile then some descriptor else none
  | none =>
      match codecV2.decode bytes with
      | some descriptor =>
          if descriptor.legacyProfile then none else some descriptor
      | none => none

/-- Stable physical image identity for the exact raw signed-SPK bytes.
The host must still verify the raw SHA-256 from its single Bread parse and
bind the launched immutable image to those bytes. -/
def Descriptor.imageIdentity (descriptor : Descriptor) : List UInt8 :=
  "DREGG/SPK-IMAGE/v1".toUTF8.toList ++ descriptor.rawSha256

/-- Sandstorm's signing-key App ID is a 52-character unpadded encoding of a
32-byte Ed25519 public key in this exact alphabet (Bread `spk.rs::base32`). -/
def appIdAlphabet : List UInt8 :=
  "0123456789acdefghjkmnpqrstuvwxyz".toUTF8.toList

theorem decode_encode (descriptor : Descriptor) :
    codec.decode (codec.encode descriptor) = some descriptor :=
  codec.decode_encode descriptor

theorem decode_encode_v2 (descriptor : Descriptor) :
    codecV2.decode (codecV2.encode descriptor) = some descriptor :=
  codecV2.decode_encode descriptor

theorem decoded_canonical {bytes : List UInt8} {descriptor : Descriptor}
    (decoded : codec.decode bytes = some descriptor) :
    codec.encode descriptor = bytes :=
  NativeHostCodec.framed_canonical _ descriptorStream decoded

theorem decoded_canonical_v2 {bytes : List UInt8} {descriptor : Descriptor}
    (decoded : codecV2.decode bytes = some descriptor) :
    codecV2.encode descriptor = bytes :=
  NativeHostCodec.framed_canonical _ descriptorStream decoded

theorem legacy_codec_injective : Function.Injective codec.encode :=
  lawful_encode_injective codec

theorem bytes_injective_v2 : Function.Injective codecV2.encode :=
  lawful_encode_injective codecV2

theorem legacy_canonical_bytes (descriptor : Descriptor)
    (legacy : descriptor.legacyProfile = true) :
    descriptor.canonicalBytes = codec.encode descriptor := by
  simp [Descriptor.canonicalBytes, legacy]

theorem new_profile_canonical_bytes (descriptor : Descriptor)
    (newProfile : descriptor.legacyProfile = false) :
    descriptor.canonicalBytes = codecV2.encode descriptor := by
  simp [Descriptor.canonicalBytes, newProfile]

theorem v1_frame_refuses_new_profile (descriptor : Descriptor)
    (newProfile : descriptor.legacyProfile = false) :
    decodeCanonical (codec.encode descriptor) = none := by
  simp [decodeCanonical, codec.decode_encode, newProfile]

/-- The exact byte grammar shared with `native/signed-api-path`: each interior
segment is nonempty ASCII `[A-Za-z0-9._~-]`, excluding `.` and `..`. This
does not decode percent escapes, normalize slashes, or interpret URL syntax. -/
def safeApiByte (byte : UInt8) : Bool :=
  let n := byte.toNat
  decide ((48 ≤ n ∧ n ≤ 57) ∨ (65 ≤ n ∧ n ≤ 90) ∨
    (97 ≤ n ∧ n ≤ 122) ∨ n = 45 ∨ n = 95 ∨ n = 46 ∨ n = 126)

def safeApiSegment (reversed : List UInt8) : Bool :=
  !reversed.isEmpty && reversed != [46] && reversed != [46, 46]

/-- Parse literal segments up to and including the required final slash.
The accumulator is reversed so recursion is structural on the input bytes. -/
def safeApiTail (reversed : List UInt8) : List UInt8 → Bool
  | [] => false
  | byte :: rest =>
      if byte == 47 then
        safeApiSegment reversed && (rest.isEmpty || safeApiTail [] rest)
      else
        safeApiByte byte && safeApiTail (byte :: reversed) rest

/-- Signed API prefix profile: `/` or a literal slash-terminated path of at
most 256 bytes. Empty means no API and is deliberately not a prefix. -/
def validApiPrefix (path : List UInt8) : Bool :=
  decide (path.length ≤ 256) &&
  (path == [47] ||
    match path with
    | 47 :: rest => safeApiTail [] rest
    | _ => false)

theorem validApiPrefix_root : validApiPrefix [47] = true := by decide

theorem validApiPrefix_gitweb :
    validApiPrefix [47, 114, 101, 112, 111, 46, 103, 105, 116, 47] = true := by decide

theorem validApiPrefix_other_literal :
    validApiPrefix [47, 97, 112, 105, 47, 118, 49, 46, 95, 45, 126, 47] = true := by decide

theorem validApiPrefix_ambiguous_refused :
    validApiPrefix [47, 47] = false ∧
    validApiPrefix [47, 97, 112, 105, 47, 47] = false ∧
    validApiPrefix [47, 46, 47] = false ∧
    validApiPrefix [47, 46, 46, 47] = false ∧
    validApiPrefix [47, 97, 112, 105, 47, 37, 50, 101, 47] = false ∧
    validApiPrefix [47, 97, 112, 105, 92, 47] = false ∧
    validApiPrefix [47, 97, 112, 105, 63, 47] = false := by decide

theorem validApiPrefix_empty : validApiPrefix [] = false := by decide

theorem validApiPrefix_bounded (path : List UInt8)
    (valid : validApiPrefix path = true) : path.length ≤ 256 := by
  simp only [validApiPrefix, Bool.and_eq_true, decide_eq_true_eq] at valid
  exact valid.1

/-- The historical v1 bridge mapping. Its accepted bytes and root remain
unchanged for GitWeb and web-only packages. -/
def Descriptor.validBridgeMappingV1 (descriptor : Descriptor) : Bool :=
  match descriptor.interfaces with
  | [web] =>
      web.id == 1 && web.version == 1 && web.kind == .web &&
      descriptor.bridgeApiPath.isEmpty
  | [web, api] =>
      web.id == 1 && web.version == 1 && web.kind == .web &&
      api.id == 2 && api.version == 1 && api.kind == .api &&
      api.schema == web.schema &&
      descriptor.bridgeApiPath == "/repo.git/".toUTF8.toList
  | _ => false

/-- V2 permits exactly the same ordered Mini interface projection for any
canonical signed API prefix. The signed package still supplies the path and
schema; it does not choose Mini ids, kinds or versions. -/
def Descriptor.validBridgeMappingV2 (descriptor : Descriptor) : Bool :=
  match descriptor.interfaces with
  | [web] =>
      web.id == 1 && web.version == 1 && web.kind == .web &&
      descriptor.bridgeApiPath.isEmpty
  | [web, api] =>
      web.id == 1 && web.version == 1 && web.kind == .web &&
      api.id == 2 && api.version == 1 && api.kind == .api &&
      api.schema == web.schema && validApiPrefix descriptor.bridgeApiPath
  | _ => false

/-- Profile selection is deterministic from the signed bytes: v1 keeps its
old GitWeb/no-API acceptance, while every other path must satisfy v2. -/
def Descriptor.validBridgeMapping (descriptor : Descriptor) : Bool :=
  if descriptor.legacyProfile then descriptor.validBridgeMappingV1
  else descriptor.validBridgeMappingV2

theorem legacy_mapping_unchanged (descriptor : Descriptor)
    (legacy : descriptor.legacyProfile = true) :
    descriptor.validBridgeMapping = descriptor.validBridgeMappingV1 := by
  simp [Descriptor.validBridgeMapping, legacy]

theorem v2_api_has_canonical_prefix (descriptor : Descriptor)
    (web api : ApplicationDispatchManifest.Interface)
    (interfaces : descriptor.interfaces = [web, api])
    (valid : descriptor.validBridgeMappingV2 = true) :
    validApiPrefix descriptor.bridgeApiPath = true := by
  simp only [Descriptor.validBridgeMappingV2, interfaces, Bool.and_eq_true] at valid
  aesop

/-- The source parser and physical host share this exact bounded shape.
Twenty-six-bit/felt folds are not used anywhere in this identity. -/
def Descriptor.valid (descriptor : Descriptor) : Bool :=
  decide (descriptor.rawSha256.length = 32) &&
  decide (0 < descriptor.rawLength ∧ descriptor.rawLength ≤ 256 * 1024 * 1024) &&
  decide (descriptor.signedAppId.length = 52) &&
  descriptor.signedAppId.all (fun byte => appIdAlphabet.contains byte) &&
  decide (descriptor.manifestSha256.length = 32) &&
  decide (descriptor.bridgeConfigSha256.length = 32) &&
  descriptor.validBridgeMapping &&
  decide ((descriptor.interfaces.map ApplicationDispatchManifest.Interface.id).Nodup) &&
  descriptor.interfaces.all (fun interface => interface.schema.valid)

/-- Domain separation makes this a commitment to the entire canonical v1
descriptor, rather than to a human-readable SHA-256 string alone. -/
def Descriptor.root (descriptor : Descriptor) : Digest :=
  (Sp800185Cshake256.hash
    (if descriptor.legacyProfile then
      "DREGG/APPLICATION/SPK-PACKAGE-ROOT/v1".toUTF8.toList
     else "DREGG/APPLICATION/SPK-PACKAGE-ROOT/v2".toUTF8.toList)
    descriptor.canonicalBytes).digest

/-- A full raw SHA-256 output is mapped to the repository's little-endian
`Digest` carrier exactly, only as an auxiliary inspection value. The package
root above additionally commits size, signed key, manifest, bridge and schema. -/
def Descriptor.rawShaDigest (descriptor : Descriptor) : Digest :=
  Sp800185Cshake256.digestOfBytesLE descriptor.rawSha256

theorem rawSha_bytes_exact (descriptor : Descriptor)
    (valid : descriptor.valid = true) :
    Sp800185Cshake256.digestBytesLE descriptor.rawShaDigest =
      descriptor.rawSha256 := by
  have length : descriptor.rawSha256.length = 32 := by
    simp only [Descriptor.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
    aesop
  exact Sp800185Cshake256.digestBytesLE_digestOfBytesLE _ length

/-- The installed Mini manifest must name precisely this signed package and
the ordered interface/schema projection derived from the same SPK. Mini's
`packageVersion` is an installation sequence (initial install 0 → 1), whereas
`signedAppVersion` is publisher metadata (GitWeb is 10); the latter is already
bound inside `root` and must not be equated with the former. A v2 lifecycle
receiver must require these bytes and relation at install and claim; this
pure predicate alone is not a physical attestation. -/
def Descriptor.matchesManifest (descriptor : Descriptor)
    (manifest : ApplicationDispatchManifest.Manifest) : Bool :=
  descriptor.valid &&
  decide (manifest.packageRoot = descriptor.root) &&
  decide (manifest.interfaces = descriptor.interfaces) &&
  manifest.valid

end Minidregg.Kernel.ApplicationSpkPackageIdentity
