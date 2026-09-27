/-
Strict JSON authoring for the role-relevant Sandstorm ViewInfo projection.
The JSON came from an app capability and is untrusted. This module only emits
canonical descriptor bytes; it does not install them or authorize a session.
The eventual Host.Json entry must call its duplicate-key-safe `parse` first.
-/
import Kernel.ApplicationPermissionSchema
import Lean.Data.Json

namespace Minidregg.Host.ApplicationPermissionSchemaAuthoring
open Lean
open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.ApplicationPermissionSchema
open Minidregg.Compiler.Tower256ConcreteBackend
set_option autoImplicit false

abbrev Result := Except String

private def exactObject (path : String) (fields : List String)
    (json : Json) : Result (Std.TreeMap.Raw String Json compare) := do
  let obj ← json.getObj?.mapError (fun _ => s!"{path}: object expected")
  let actual := obj.foldl (init := []) (fun names key _ => key :: names)
  for field in fields do
    unless actual.contains field do throw s!"{path}: missing field {field}"
  for field in actual do
    unless fields.contains field do throw s!"{path}: unknown field {field}"
  pure obj

private def field (path key : String)
    (obj : Std.TreeMap.Raw String Json compare) : Result Json :=
  match obj.get? key with
  | some value => pure value
  | none => throw s!"{path}: missing field {key}"

private def text (path : String) (json : Json) : Result String :=
  json.getStr?.mapError (fun _ => s!"{path}: string expected")

private def boolean (path : String) (json : Json) : Result Bool :=
  json.getBool?.mapError (fun _ => s!"{path}: boolean expected")

private def canonicalNat (path : String) (json : Json) : Result Nat := do
  let source ← text path json
  match source.toNat? with
  | some value =>
      if toString value = source then pure value
      else throw s!"{path}: canonical unsigned decimal string expected"
  | none => throw s!"{path}: unsigned decimal string expected"

private def boundedArray (path : String) (maximum : Nat)
    (json : Json) : Result (Array Json) := do
  let values ← json.getArr?.mapError (fun _ => s!"{path}: array expected")
  if values.size > maximum then throw s!"{path}: exceeds bound"
  pure values

private def permission (json : Json) : Result Permission := do
  let obj ← exactObject "permission" ["name", "obsolete"] json
  let name ← text "permission.name" (← field "permission" "name" obj)
  if name.utf8ByteSize > 256 then throw "permission.name: exceeds bound"
  pure ⟨name.toUTF8.toList,
    ← boolean "permission.obsolete" (← field "permission" "obsolete" obj)⟩

private def role (permissionCount : Nat) (json : Json) : Result Role := do
  let obj ← exactObject "role" ["permissions", "obsolete", "default"] json
  let raw ← boundedArray "role.permissions" permissionCount
    (← field "role" "permissions" obj)
  let mut bits := []
  for value in raw do
    bits := bits ++ [← boolean "role.permissions[]" value]
  pure ⟨bits,
    ← boolean "role.obsolete" (← field "role" "obsolete" obj),
    ← boolean "role.default" (← field "role" "default" obj)⟩

/-- Exact projection input contract for the private fd3 adapter. A schema
version is supplied explicitly by the controller; ViewInfo has no such field.
All arrays are bounded and any unknown field is refused. -/
def decodeSource (json : Json) : Result Schema := do
  let obj ← exactObject "schema"
    ["type", "version", "permissions", "roles", "denied"] json
  let kind ← text "schema.type" (← field "schema" "type" obj)
  unless kind = "minidregg-application-permission-schema-source-v1" do
    throw "schema.type: wrong source kind"
  let version ← canonicalNat "schema.version" (← field "schema" "version" obj)
  let rawPermissions ← boundedArray "schema.permissions" 256
    (← field "schema" "permissions" obj)
  let mut permissions := []
  for value in rawPermissions do
    permissions := permissions ++ [← permission value]
  let rawRoles ← boundedArray "schema.roles" 256 (← field "schema" "roles" obj)
  let mut roles := []
  for value in rawRoles do
    roles := roles ++ [← role permissions.length value]
  let rawDenied ← boundedArray "schema.denied" permissions.length
    (← field "schema" "denied" obj)
  let mut denied := []
  for value in rawDenied do
    denied := denied ++ [← boolean "schema.denied[]" value]
  let schema : Schema := ⟨version, permissions, roles, denied⟩
  unless schema.valid do throw "schema: invalid names, masks, defaults, or version"
  pure schema

/-- Canonical bytes and root for a syntactically valid descriptor. The caller
must still bind these bytes to a governed installed interface. -/
def author (json : Json) : Result (List UInt8 × Digest) := do
  let schema ← decodeSource json
  pure (schemaCodec.encode schema, schema.root)

end Minidregg.Host.ApplicationPermissionSchemaAuthoring
