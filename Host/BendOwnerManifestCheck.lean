/- Executed ingress conformance/refusal checks; no universal crypto claim. -/
import Host.BendOwnerManifestJson
namespace Minidregg.Host.BendOwnerManifestCheck
open Lean
open Minidregg.Host.BendOwnerManifestJson
def fields : List (String × Json) :=
  [("schema", .str schema), ("profile", .str literalProfile),
   ("parameters_sha256", .str (String.ofList (List.replicate 64 '0'))),
   ("transformer_sha256", .str (String.ofList (List.replicate 64 '1'))),
   ("public_key", .str "01"),
   ("key_epoch", .str (String.ofList (List.replicate 64 '2')))]
def replaceField (name : String) (value : Json) : List (String × Json) :=
  fields.map fun pair => if pair.1 = name then (name, value) else pair
def refuses (source : String) : IO Unit :=
  match parse source with
  | .error _ => pure ()
  | .ok _ => throw <| IO.userError "malformed public material was accepted"
def run : IO Unit := do
  let args ← IO.getArgs
  unless args.size = 1 do throw <| IO.userError "expected actual public manifest path"
  let actual ← IO.FS.readFile args[0]!
  let material ← IO.ofExcept (parse actual)
  unless material.publicKey.length > 0 do throw <| IO.userError "actual public key lost"
  let minimal := (Json.mkObj fields).compress
  let _ ← IO.ofExcept (parse minimal)
  refuses ((Json.mkObj (fields ++ [("extra", .str "unknown")])).compress)
  refuses ((Json.mkObj (fields.filter (fun pair => pair.1 != "key_epoch"))).compress)
  refuses ((Json.mkObj (replaceField "public_key" (.str "aB"))).compress)
  refuses ((Json.mkObj (replaceField "public_key" (.str "0"))).compress)
  refuses ((Json.mkObj (replaceField "public_key" (.str ""))).compress)
  refuses ((Json.mkObj (replaceField "parameters_sha256" (.str "00"))).compress)
  refuses ((Json.mkObj (replaceField "profile" (.str "unregistered-profile"))).compress)
  refuses ((Json.mkObj (replaceField "profile" (.str muxProfile))).compress)
  refuses ((Json.mkObj (fields ++ [("relinearization_key", .str "01")])).compress)
  refuses (minimal.replace "{" "{\"schema\":\"duplicate\",")
  refuses (minimal.replace "{" "{\"schem\\u0061\":\"duplicate\",")
  refuses (String.ofList (List.replicate (maxSourceBytes + 1) ' '))
  let muxFields := replaceField "profile" (.str muxProfile) ++ [("relinearization_key", .str "01")]
  let mux ← IO.ofExcept (parse (Json.mkObj muxFields).compress)
  unless mux.relinearizationKey = some [1] do
    throw <| IO.userError "mux required key bytes lost"
  IO.println "BEND-OWNER-MANIFEST: actual public material, duplicate/escaped alias/unknown/missing/profile/hex/width/cap refusals PASS"
end Minidregg.Host.BendOwnerManifestCheck
def main : IO Unit := Minidregg.Host.BendOwnerManifestCheck.run
