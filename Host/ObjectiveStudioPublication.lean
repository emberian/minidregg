/- `lean --run` entry for Objective source publication: inspect an imported
package/artifact pair, replay a package's module sources, or author a
publication payload. The payload author is `Host.ObjectivePackageAuthor.author`
(also the native Host's `objective-publication` operation). -/
import Host.ObjectivePackageAuthor

open Lean

def main (args : List String) : IO UInt32 := do
  if let ["inspect",packagePath,artifactPath,directoryPath] := args then
    try
      let directory := System.FilePath.mk directoryPath
      if ← directory.pathExists then IO.eprintln "inspection directory already exists";return (2 : UInt32)
      for (path,limit) in [(packagePath,12582912),(artifactPath,4198400)] do
        if (← (System.FilePath.mk path).metadata).byteSize > UInt64.ofNat limit then
          IO.eprintln "imported source byte capacity";return (2 : UInt32)
      let packageBytes ← IO.FS.readBinFile packagePath
      let artifactBytes ← IO.FS.readBinFile artifactPath
      let some package := Minidregg.Compiler.ObjectiveSourcePackage.decode packageBytes.toList | do
        IO.eprintln "canonical imported Objective package required";return (2 : UInt32)
      let some artifact := Minidregg.Compiler.ObjectiveBendSourceArtifact.decode artifactBytes.toList | do
        IO.eprintln "canonical imported source artifact required";return (2 : UInt32)
      if artifact.package != Minidregg.Compiler.ObjectiveSourcePackage.identity package ||
          Minidregg.Compiler.ObjectiveSourcePackage.selectedDeclaration package != some artifact.declaration then
        IO.eprintln "imported package/artifact selection mismatch";return (2 : UInt32)
      if artifact.inputCodec != Minidregg.Kernel.ObjectiveBendNativeInput.codecId then
        IO.eprintln "imported native input codec differs";return (2 : UInt32)
      IO.FS.createDirAll directory
      IO.FS.writeBinFile (directory / "offered-core.json") ⟨artifact.typedCore.toArray⟩
      IO.FS.writeBinFile (directory / "offered-output-codec.bin") ⟨(Minidregg.Compiler.Tower256ConcreteBackend.digestStream.encode artifact.outputCodec).toArray⟩
      IO.println <| (Lean.Json.mkObj [("schema",toJson "mini-studio-imported-source-v1"),
        ("packageId",toJson (toString artifact.package.value)),("artifactId",toJson (toString (Minidregg.Compiler.ObjectiveBendSourceArtifact.identity artifact).value)),
        ("sourceEntry",toJson artifact.declaration),("authority",toJson "none; independent source replay and current native opening required")]).compress
      return (0 : UInt32)
    catch error => IO.eprintln error.toString;return (2 : UInt32)
  if let ["replay",packagePath,directoryPath] := args then
    try
      let directory := System.FilePath.mk directoryPath
      if ← directory.pathExists then IO.eprintln "replay directory already exists";return (2 : UInt32)
      let raw ← IO.FS.readBinFile packagePath
      if raw.size > 12582912 then IO.eprintln "package byte capacity";return (2 : UInt32)
      let some package := Minidregg.Compiler.ObjectiveSourcePackage.decode raw.toList | do
        IO.eprintln "canonical Objective package required";return (2 : UInt32)
      if !Minidregg.Compiler.ObjectiveSourcePackage.wellFormed package then IO.eprintln "package structure refusal";return (2 : UInt32)
      IO.FS.createDirAll directory
      let mut modules : List Json := []
      for index in List.range package.modules.length do
        let some module := package.modules[index]? | throw (IO.userError "package module index")
        let path := directory / s!"module-{index}.obend"
        IO.FS.writeBinFile path ⟨module.source.toArray⟩
        modules := modules ++ [Json.mkObj [("name",toJson module.name),("sourcePath",toJson path.toString),
          ("imports",toJson (module.imports.map fun edge => Json.mkObj [("alias",toJson edge.importAlias),
            ("path",toJson edge.path),("module",toJson (toString edge.target))]))]]
      let input := Json.mkObj [("schema",toJson "dregg.objective-bend.package-input.v1"),
        ("edition",toJson "objective-bend-1"),("modules",toJson modules),
        ("entryModule",toJson (toString package.entryModule)),("entryDefinition",toJson package.entryDefinition)]
      IO.FS.writeFile (directory / "package-input.json") input.compress
      IO.println input.compress
      return (0 : UInt32)
    catch error => IO.eprintln error.toString;return (2 : UInt32)
  let [packagePath,replayedPackagePath,offeredPath,expectedPath,codecPath,outputPath] := args | do
    IO.eprintln "usage: objective-studio-publication PACKAGE_BIN REPLAYED_PACKAGE_BIN OFFERED_CANONICAL_CORE REPLAYED_CANONICAL_CORE NATIVE_OUTPUT_CODEC_BIN NEW_PAYLOAD_JSON"
    return (2 : UInt32)
  try
    if ← (System.FilePath.mk outputPath).pathExists then IO.eprintln "publication output already exists";return (2 : UInt32)
    let read (path : String) (limit : Nat) : IO (List UInt8) := do
      let metadata ← (System.FilePath.mk path).metadata
      if metadata.byteSize > UInt64.ofNat limit then throw (IO.userError "source publication file capacity")
      pure (← IO.FS.readBinFile path).toList
    let package ← read packagePath 12582912
    let replayedPackage ← read replayedPackagePath 12582912
    let offered ← read offeredPath 4194304
    let expected ← read expectedPath 4194304
    let codec ← read codecPath 1024
    match Minidregg.Host.ObjectivePackageAuthor.author package replayedPackage offered expected codec with
    | .error reason => IO.eprintln reason;return (2 : UInt32)
    | .ok json => IO.FS.writeFile outputPath json.compress;IO.println json.compress;return (0 : UInt32)
  catch error => IO.eprintln error.toString;return (2 : UInt32)
