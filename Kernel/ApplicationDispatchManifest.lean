/-
Canonical selected-interface meaning for application dispatch. This is a
descriptor format and pure matching relation, not a claim that a caller's
descriptor is installed. The native receiver must read the governed current
package-manifest content cell, decode these bytes there, and bind its exact
cell root before using `matches`; birth/version numbers alone do not do so.
-/
import Kernel.ApplicationDispatchCodec
import Kernel.ApplicationPermissionSchema

namespace Minidregg.Kernel.ApplicationDispatchManifest

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.Hyperdocument
open Minidregg.Kernel.ApplicationDispatchCodec
open Minidregg.Kernel.ApplicationPermissionSchema

set_option autoImplicit false

/-- The full ordered role-relevant ViewInfo projection is bound to each
interface. Bit `i` names permission `i`; web and API interface kinds remain
distinct. This descriptor is not itself an installed grant. -/
structure Interface where
  id : Nat
  version : Nat
  kind : InterfaceKind
  schema : Schema
  deriving DecidableEq, Repr

def interfaceStream : StreamCodec Interface :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product interfaceKindStream
          schemaStream)))
    (fun interface => (interface.id, interface.version,
      interface.kind, interface.schema))
    (fun (interfaceId, version, kind, schema) =>
      ⟨interfaceId, version, kind, schema⟩)
    (by intro interface; cases interface; rfl)

private def interfaceFrame : List UInt8 :=
  "DREGG/APPLICATION/INTERFACE/v2".toUTF8.toList

private def rawInterfaceCodec : LawfulCodec Interface where
  encode interface := interfaceFrame ++ interfaceStream.encode interface
  decode bytes := if bytes.take interfaceFrame.length = interfaceFrame then
    interfaceStream.toLawful.decode (bytes.drop interfaceFrame.length) else none
  decode_encode := by
    intro interface
    have decoded := interfaceStream.toLawful.decode_encode interface
    change interfaceStream.toLawful.decode (interfaceStream.encode interface) =
      some interface at decoded
    simp [decoded]

def interfaceCodec : LawfulCodec Interface :=
  ResourceBirthCodec.strictCodec rawInterfaceCodec

def Interface.root (interface : Interface) : Digest :=
  (Sp800185Cshake256.hash "DREGG/APPLICATION/INTERFACE-ROOT/v2".toUTF8.toList
    (interfaceCodec.encode interface)).digest

def Interface.permissionSchemaRoot (interface : Interface) : Digest :=
  interface.schema.root

structure Manifest where
  app : Nat
  packageVersion : Int
  packageRoot : Digest
  interfaces : List Interface
  deriving DecidableEq, Repr

def manifestStream : StreamCodec Manifest :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product IntStream.intStream
        (StreamCodec.product digestStream (StreamCodec.list interfaceStream))))
    (fun manifest => (manifest.app, manifest.packageVersion,
      manifest.packageRoot, manifest.interfaces))
    (fun (app, packageVersion, packageRoot, interfaces) =>
      ⟨app, packageVersion, packageRoot, interfaces⟩)
    (by intro manifest; cases manifest; rfl)

private def manifestFrame : List UInt8 :=
  "DREGG/APPLICATION/MANIFEST/v2".toUTF8.toList

private def rawManifestCodec : LawfulCodec Manifest where
  encode manifest := manifestFrame ++ manifestStream.encode manifest
  decode bytes := if bytes.take manifestFrame.length = manifestFrame then
    manifestStream.toLawful.decode (bytes.drop manifestFrame.length) else none
  decode_encode := by
    intro manifest
    have decoded := manifestStream.toLawful.decode_encode manifest
    change manifestStream.toLawful.decode (manifestStream.encode manifest) = some manifest
      at decoded
    simp [decoded]

def manifestCodec : LawfulCodec Manifest :=
  ResourceBirthCodec.strictCodec rawManifestCodec

theorem manifest_decode_encode (manifest : Manifest) :
    manifestCodec.decode (manifestCodec.encode manifest) = some manifest :=
  manifestCodec.decode_encode manifest

/-- Every embedded schema is complete and unambiguous. The v1 names-only
manifest frame is refused by `manifestCodec`; no such draft was admitted. -/
def Manifest.valid (manifest : Manifest) : Bool :=
  decide ((manifest.interfaces.map Interface.id).Nodup) &&
  manifest.interfaces.all (fun interface => interface.schema.valid)

/-- One stable typed atom slot per application. A package upgrade edits this
atom's canonical payload, whose `packageVersion` is checked against the
currently witnessed app record. One stable atom keeps the manifest address
fixed across upgrades. The native receiver must still
derive the manifest resource from the governed app birth/policy and read-guard
its current physical root; a caller-supplied store is not authority. -/
def manifestAtom (domain : Digest) (app : Nat) : AtomId :=
  let preimage := (StreamCodec.product digestStream StreamCodec.nat).encode (domain, app)
  ⟨⟨(Sp800185Cshake256.hash
    "DREGG/APPLICATION/MANIFEST-ATOM/v1".toUTF8.toList preimage).digest.value⟩⟩

def decodeInstalled (domain : Digest) (manifestResource app : Nat) (version : Int)
    (page : ContentResource.ContentStore) : Option Manifest := do
  let record ← Hyperdocument.lookup page .atoms
    (manifestAtom domain app)
  if record.document != ⟨⟨manifestResource⟩⟩ || record.kind != .inlineObject ⟨13⟩ ||
      record.tombstonedAt.isSome then none else
  let manifest ← manifestCodec.decode record.payload
  if manifest.app == app && manifest.packageVersion == version && manifest.valid then
    some manifest
  else none

def Manifest.select (manifest : Manifest) (id : Nat) : Option Interface :=
  manifest.interfaces.find? (fun interface => interface.id == id)

/-- This checks descriptor identity and bit-vector width only. It is not
permission authorization. Sandstorm role assignments can mean none/default,
all-access or a role plus added/removed permissions; powerbox API connections
have separate fixed/captured permission semantics. A future checked receiver
must resolve that exact selected profile against current grants and compare
the resulting bits with `Dispatch.identity`. It must first obtain `manifest`
from the current read-guarded installed content cell. -/
def matchesDispatch (manifest : Manifest) (dispatch : Dispatch) : Bool :=
  manifest.valid &&
  decide (manifest.app = dispatch.app.resource) &&
  decide (manifest.packageVersion = dispatch.app.packageVersion) &&
  decide (manifest.packageRoot = dispatch.app.packageRoot) &&
  match manifest.select dispatch.app.interfaceId with
  | none => false
  | some interface =>
      decide (interface.version = dispatch.app.interfaceVersion) &&
      decide (interface.kind = dispatch.session.kind) &&
      decide (interface.root = dispatch.app.interfaceRoot) &&
      decide (interface.permissionSchemaRoot = dispatch.identity.permissionSchemaRoot) &&
      decide (dispatch.identity.permissionBits < 2 ^ interface.schema.permissions.length)

theorem matches_app (manifest : Manifest) (dispatch : Dispatch)
    (accepted : matchesDispatch manifest dispatch = true) :
    manifest.app = dispatch.app.resource := by
  simp [matchesDispatch, Bool.and_eq_true] at accepted
  aesop

end Minidregg.Kernel.ApplicationDispatchManifest
