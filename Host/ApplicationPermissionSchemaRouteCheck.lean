/- Executable route check. General codec and resolution laws live in Kernel. -/
import Host.Json
import Kernel.ApplicationDispatchManifest

namespace Minidregg.Host.ApplicationPermissionSchemaRouteCheck

open Lean
open Minidregg.Kernel.ApplicationPermissionSchema
open Minidregg.Kernel.ApplicationGrainSessionEnrollment
open Minidregg.Kernel.ApplicationDispatchManifest

private def authored (source : String) : IO (List UInt8) := do
  let json ← IO.ofExcept (Json.parse source)
  let parsed ← IO.ofExcept (Minidregg.Host.Json.parse source)
  unless json == parsed do
    throw (IO.userError "host JSON parser changed the schema source")
  IO.ofExcept (Minidregg.Host.Json.author "application-permission-schema" parsed)

def main : IO Unit := do
  let source ← IO.FS.readFile "native/spk-rpc/tests/fixtures/permission-schema-source-v1.json"
  let bytes ← authored source
  let schema ← match schemaCodec.decode bytes with
    | some value => pure value
    | none => throw (IO.userError "route did not emit canonical schema bytes")
  let rendered ← IO.ofExcept (Minidregg.Host.Json.inspect
    "application-permission-schema" bytes)
  let renderedObj ← IO.ofExcept rendered.getObj?
  unless renderedObj.get? "root" == some (.str (toString schema.root.value)) &&
      renderedObj.get? "version" == some (.str "7") do
    throw (IO.userError "inspected root/version differs from canonical schema")
  let roleSource := source.replace "\"default\": true" "\"default\": false"
  let deniedSource := source.replace "\"denied\": [false, true]"
    "\"denied\": [false, false]"
  unless roleSource != source && deniedSource != source do
    throw (IO.userError "fixture no longer exercises role and denial changes")
  let roleBytes ← authored roleSource
  let deniedBytes ← authored deniedSource
  let some roleSchema := schemaCodec.decode roleBytes
    | throw (IO.userError "role variant decode refused")
  let some deniedSchema := schemaCodec.decode deniedBytes
    | throw (IO.userError "denied variant decode refused")
  unless schema.root != roleSchema.root && schema.root != deniedSchema.root do
    throw (IO.userError "full role/denied metadata is not bound by schema root")
  let originalAll : RoleAssignment := ⟨.allAccess, [], [], schema.root, 7⟩
  let deniedAll : RoleAssignment := ⟨.allAccess, [], [], deniedSchema.root, 7⟩
  unless schema.resolve originalAll == some [true, true] &&
      deniedSchema.resolve deniedAll == schema.resolve originalAll do
    throw (IO.userError "informational denied metadata altered role bits")
  let interface : Interface := ⟨1, 7, .web, schema⟩
  unless interface.permissionSchemaRoot == schema.root &&
      interfaceCodec.decode (interfaceCodec.encode interface) == some interface do
    throw (IO.userError "installed interface did not bind full schema")
  let manifest : Manifest := ⟨9, 2, schema.root, [interface]⟩
  let legacy := "DREGG/APPLICATION/MANIFEST/v1".toUTF8.toList ++
    manifestStream.encode manifest
  unless manifest.valid &&
      manifestCodec.decode (manifestCodec.encode manifest) == some manifest &&
      manifestCodec.decode legacy == none do
    throw (IO.userError "v2 manifest failed canonical or legacy-frame gate")
  match Minidregg.Host.Json.parse "{\"version\":\"7\",\"version\":\"8\"}" with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "duplicate-key JSON was accepted")
  IO.println "application permission schema route: ok"

#eval main

end Minidregg.Host.ApplicationPermissionSchemaRouteCheck
