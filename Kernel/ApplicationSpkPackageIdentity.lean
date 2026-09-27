/-
Source-owned identity for an actual signature-verified Sandstorm SPK image.
The physical host must derive every field from the same bounded, verified
package parse before it accepts a lifecycle install/claim. A naked SHA-256
decimal value or caller-asserted interface schema is not a package identity.
The v1 descriptor has no optional or alternative layouts.
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

def Descriptor.canonicalBytes (descriptor : Descriptor) : List UInt8 :=
  codec.encode descriptor

/-- Sandstorm's signing-key App ID is a 52-character unpadded encoding of a
32-byte Ed25519 public key in this exact alphabet (Bread `spk.rs::base32`). -/
def appIdAlphabet : List UInt8 :=
  "0123456789acdefghjkmnpqrstuvwxyz".toUTF8.toList

theorem decode_encode (descriptor : Descriptor) :
    codec.decode descriptor.canonicalBytes = some descriptor :=
  codec.decode_encode descriptor

theorem decoded_canonical {bytes : List UInt8} {descriptor : Descriptor}
    (decoded : codec.decode bytes = some descriptor) :
    descriptor.canonicalBytes = bytes :=
  NativeHostCodec.framed_canonical _ descriptorStream decoded

theorem bytes_injective : Function.Injective Descriptor.canonicalBytes :=
  lawful_encode_injective codec

/-- Initial bridge mapping: Mini web id 1/v1, and optionally Mini API id 2/v1
with the same signed ViewInfo schema. The API path is the exact signed bridge
path, restricted to GitWeb's `/repo.git/` in this v1 profile. A different API
path needs a new checked adapter profile, never an implicit URL prefix. -/
def Descriptor.validBridgeMapping (descriptor : Descriptor) : Bool :=
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
    "DREGG/APPLICATION/SPK-PACKAGE-ROOT/v1".toUTF8.toList
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
