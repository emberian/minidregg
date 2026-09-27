/- A bounded source-owned projection of the already signature-verified GitWeb
SPK and decoded signed BridgeConfig. This authors canonical Mini bytes/roots;
it does not perform SPK signature verification or install a Mini manifest. -/
import Host.ApplicationPermissionSchemaAuthoring
import Kernel.ApplicationSpkPackageIdentity

open Lean
open Minidregg.Compiler
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.ApplicationPermissionSchema
open Minidregg.Kernel.ApplicationDispatchManifest
open Minidregg.Kernel.ApplicationSpkPackageIdentity

private def fail (detail : String) : IO α := throw (IO.userError detail)

private def field (json : Json) (name : String) : IO Json :=
  IO.ofExcept ((json.getObjVal? name).mapError toString)

private def stringField (json : Json) (name : String) : IO String := do
  IO.ofExcept (((← field json name).getStr?).mapError toString)

private def decimalField (json : Json) (name : String) : IO Nat := do
  let source ← stringField json name
  let some value := source.toNat? | fail s!"{name}: decimal expected"
  if toString value != source then fail s!"{name}: noncanonical decimal"
  pure value

private def exactFields (json : Json) (wanted : List String) : IO Unit := do
  let obj ← IO.ofExcept (json.getObj?.mapError toString)
  let actual := obj.foldl (init := []) (fun names key _ => key :: names)
  unless actual.length == wanted.length &&
      actual.all (wanted.contains ·) && wanted.all (actual.contains ·) do
    fail "GitWeb input has missing or unexpected fields"

private def signedSchema : Schema :=
  ⟨10,
    [⟨"read".toUTF8.toList, false⟩, ⟨"write".toUTF8.toList, false⟩],
    [⟨[true, false], false, false⟩, ⟨[true, true], false, true⟩], []⟩

private def nibble (char : Char) : Option Nat :=
  let value := char.toNat
  if 48 ≤ value && value ≤ 57 then some (value - 48)
  else if 97 ≤ value && value ≤ 102 then some (value - 87)
  else none

private def decodeHex : List Char → Option (List UInt8)
  | [] => some []
  | first :: second :: rest => do
      let high ← nibble first
      let low ← nibble second
      let tail ← decodeHex rest
      some (UInt8.ofNat (16 * high + low) :: tail)
  | _ => none

private def exactHex (name source : String) : IO (List UInt8) :=
  match decodeHex source.toList with
  | some bytes => pure bytes
  | none => fail s!"{name}: noncanonical lowercase even-length hex expected"

private def writeBytes (path : String) (bytes : List UInt8) : IO Unit :=
  IO.FS.writeBinFile path ⟨bytes.toArray⟩

def main (args : List String) : IO Unit := do
  let [packagePath, schemaPath, outputDir] := args
    | fail "usage: author-gitweb-identity PACKAGE.json SCHEMA.json NEW-DIR"
  let package ← IO.ofExcept (Json.parse (← IO.FS.readFile packagePath))
  let schemaJson ← IO.ofExcept (Json.parse (← IO.FS.readFile schemaPath))
  exactFields package ["type", "rawSha256", "rawLength", "signedAppId",
    "signedAppVersion", "manifestSha256", "bridgeConfigSha256", "bridgeApiPath"]
  unless (← stringField package "type") = "minidregg-gitweb-verified-spk-v1" do
    fail "wrong verified package input kind"
  let rawShaHex ← stringField package "rawSha256"
  let manifestShaHex ← stringField package "manifestSha256"
  let bridgeShaHex ← stringField package "bridgeConfigSha256"
  let appId ← stringField package "signedAppId"
  let rawLength ← decimalField package "rawLength"
  let appVersion ← decimalField package "signedAppVersion"
  let apiPath ← stringField package "bridgeApiPath"
  unless rawShaHex = "2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa" &&
      manifestShaHex = "3ef23992c6ee79e5b684cec632d4552c5b34889348ae63acaaedb42b9616024f" &&
      bridgeShaHex = "49d196f64ca2ce672a378581a8376ada53b27614bba522bbaec042237f0e70a2" &&
      rawLength = 14045864 && appVersion = 10 &&
      appId = "6va4cjamc21j0znf5h5rrgnv0rpyvh1vaxurkrgknefvj0x63ash" &&
      apiPath = "/repo.git/" do
    fail "package input differs from the verified signed GitWeb selection"
  let (schemaBytes, _) ← IO.ofExcept
    (Minidregg.Host.ApplicationPermissionSchemaAuthoring.author schemaJson)
  let some schema := schemaCodec.decode schemaBytes
    | fail "source-authored schema failed canonical readback"
  unless schema == signedSchema do
    fail "schema differs from exact decoded signed BridgeConfig projection"
  let web : Interface := ⟨1, 1, .web, schema⟩
  let api : Interface := ⟨2, 1, .api, schema⟩
  let rawSha ← exactHex "rawSha256" rawShaHex
  let manifestSha ← exactHex "manifestSha256" manifestShaHex
  let bridgeSha ← exactHex "bridgeConfigSha256" bridgeShaHex
  let descriptor : Descriptor :=
    ⟨rawSha, rawLength, appId.toUTF8.toList, appVersion,
      manifestSha, bridgeSha, apiPath.toUTF8.toList, [web, api]⟩
  unless descriptor.valid do fail "source SPK descriptor invalid"
  let manifest : Manifest := ⟨8401, 1, descriptor.root, [web, api]⟩
  unless descriptor.matchesManifest manifest do fail "prospective manifest mismatch"
  if ← System.FilePath.pathExists outputDir then fail "output directory exists"
  IO.FS.createDir outputDir
  writeBytes s!"{outputDir}/schema.bin" schemaBytes
  writeBytes s!"{outputDir}/web-interface.bin" (interfaceCodec.encode web)
  writeBytes s!"{outputDir}/api-interface.bin" (interfaceCodec.encode api)
  writeBytes s!"{outputDir}/package-identity.bin" descriptor.canonicalBytes
  writeBytes s!"{outputDir}/prospective-manifest.bin" (manifestCodec.encode manifest)
  let roots := Json.mkObj
    [("schemaRoot", toJson (toString schema.root.value)),
     ("webInterfaceRoot", toJson (toString web.root.value)),
     ("apiInterfaceRoot", toJson (toString api.root.value)),
     ("packageRoot", toJson (toString descriptor.root.value)),
     ("rawShaDigest", toJson (toString descriptor.rawShaDigest.value)),
     ("app", toJson ("8401" : String)),
     ("prospectivePackageVersion", toJson ("1" : String))]
  IO.FS.writeFile s!"{outputDir}/roots.json" roots.pretty
