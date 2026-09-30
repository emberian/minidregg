/- Executable authoring/codec check against one ordered captured ViewInfo shape.
   This is a case check; the general codec and denial laws are in Kernel. -/
import Host.ApplicationPermissionSchemaAuthoring

namespace Minidregg.Host.ApplicationPermissionSchemaAuthoringCheck
open Lean
open Minidregg.Kernel.ApplicationPermissionSchema
open Minidregg.Kernel.ApplicationGrainSessionEnrollment
open Minidregg.Host.ApplicationPermissionSchemaAuthoring

private def obj (fields : List (String × Json)) : Json := .mkObj fields
private def permission (name : String) (obsolete : Bool := false) : Json :=
  obj [("name", .str name), ("obsolete", .bool obsolete)]
private def role (bits : Array Json) (default obsolete : Bool := false) : Json :=
  obj [("permissions", .arr bits), ("obsolete", .bool obsolete),
    ("default", .bool default)]

private def sample (permissions : Array Json := #[permission "read", permission "edit" true])
    (roles : Array Json := #[role #[.bool true, .bool false] true,
      role #[.bool true, .bool true] false true]) : Json :=
  obj [("type", .str "minidregg-application-permission-schema-source-v1"),
    ("version", .str "7"), ("permissions", .arr permissions),
    ("roles", .arr roles), ("denied", .arr #[.bool false, .bool true])]

private def refused (value : Json) : Bool :=
  match author value with
  | .error _ => true
  | .ok _ => false

private def checked : Bool :=
  match author sample with
  | .error _ => false
  | .ok (bytes, root) =>
      match schemaCodec.decode bytes with
      | none => false
      | some schema =>
          let noneRole : RoleAssignment := ⟨.none, [], [], root, 7⟩
          let allRole : RoleAssignment := ⟨.allAccess, [], [], root, 7⟩
          let explicit : RoleAssignment := ⟨.role 1, [], [], root, 7⟩
          let unknown : RoleAssignment := ⟨.none, ["missing".toUTF8.toList], [], root, 7⟩
          let stale : RoleAssignment := ⟨.none, [], [], root, 8⟩
          schema.permissions.map (·.name) ==
              ["read".toUTF8.toList, "edit".toUTF8.toList] &&
          schema.root == root &&
          schema.resolve noneRole == some [true, false] &&
          schema.resolve allRole == some [true, true] &&
          schema.resolve explicit == some [true, true] &&
          schema.resolve unknown == none && schema.resolve stale == none &&
          (match author (sample (roles := #[role #[.bool true] true,
              role #[.bool true, .bool true] false true])) with
            | .ok (shortBytes, shortRoot) =>
                match schemaCodec.decode shortBytes with
                | some shortSchema => shortSchema.resolve ⟨.none, [], [], shortRoot, 7⟩ ==
                    some [true, false]
                | none => false
            | .error _ => false) &&
          refused (sample #[permission "read", permission "read"]) &&
          refused (sample (roles := #[role #[.bool true] true,
            role #[.bool true, .bool true] true])) &&
          refused (sample (Array.replicate 257 (permission "read"))) &&
          refused (obj [("type", .str "minidregg-application-permission-schema-source-v1"),
            ("version", .str "07"), ("permissions", .arr #[]),
            ("roles", .arr #[]), ("denied", .arr #[])])

def main : IO Unit := do
  unless checked do throw (IO.userError "application permission schema authoring check failed")
  let source ← IO.FS.readFile "native/spk-rpc/tests/fixtures/permission-schema-source-v1.json"
  let shared ← IO.ofExcept (Json.parse source)
  let fromShared ← IO.ofExcept (author shared)
  let fromLocal ← IO.ofExcept (author sample)
  unless fromShared = fromLocal do
    throw (IO.userError "Rust ViewInfo fixture differs from Lean-authored schema")
  IO.println "application permission schema authoring: ok"

#eval main

end Minidregg.Host.ApplicationPermissionSchemaAuthoringCheck
