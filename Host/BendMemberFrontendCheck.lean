/- Actual canonical Package + captured-core receiving producer for source
editors/linkers. Uses the existing canonical package decoder and actual source
kernel admission; successful elaboration alone cannot become checked preview. -/
import Compiler.BendCoreAdmission
import Lean.Data.Json

open Lean
open Minidregg.Compiler

namespace Minidregg.Host.BendMemberFrontendCheck
open Minidregg.Compiler.Tower256ConcreteBackend
set_option autoImplicit false

def check (packageBytes coreBytes : List UInt8) (coreEntry : String) :
    Except String (BendWorldSource.Package × BendCoreAdmission.Checked) := do
  let some package := BendWorldSource.decode packageBytes | throw "noncanonical source Package bytes"
  if !BendWorldSource.wellFormed package then throw "source Package/import identities refused"
  let core ← BendCoreAdmission.canonicalize coreBytes
  let _ ← BendCoreAdmission.entry core coreEntry
  pure (package,core)

def description (package : BendWorldSource.Package) (core : BendCoreAdmission.Checked)
    (coreEntry corePath packagePath : String) : Json :=
  Json.mkObj [("schema",toJson "dregg.bend.checked-member-capture.v1"),
    ("upstream",toJson BendWorldSource.upstreamPin),("miniToolchain",toJson BendWorldSource.miniToolchain),
    ("coreEntry",toJson coreEntry),("corePath",toJson corePath),("packagePath",toJson packagePath),
    ("packageDigestEncoding",toJson "dregg.digest-stream.bytes.v1"),
    ("packageDigest",toJson ((digestStream.encode (BendWorldSource.packageId package)).map UInt8.toNat)),
    ("canonicalCore",toJson true),("bookChecked",toJson true),
    ("coreDefinitionCount",toJson core.book.length),
    ("frontendProofScope",toJson "actual captured elaboration; no universal TypeScript compiler theorem")]

end Minidregg.Host.BendMemberFrontendCheck

def main (args : List String) : IO UInt32 := do
  let [packagePath,emittedPath,coreEntry,outputDirectory] := args | do
    IO.eprintln "usage: bend-member-check PACKAGE_BYTES EMITTED_BOOK CORE_ENTRY OUTPUT_DIRECTORY"
    return (2 : UInt32)
  try
    let packageBytes ← IO.FS.readBinFile packagePath
    let emittedBytes ← IO.FS.readBinFile emittedPath
    IO.FS.createDirAll outputDirectory
    match Minidregg.Host.BendMemberFrontendCheck.check packageBytes.toList emittedBytes.toList coreEntry with
    | .error reason =>
      let diagnostic := Json.mkObj [("schema",toJson "dregg.bend.compiler-diagnostic.v1"),
        ("stage",toJson "mini-core-admission"),("message",toJson reason)]
      IO.FS.writeFile (outputDirectory ++ "/diagnostic.json") (diagnostic.compress ++ "\n")
      return (2 : UInt32)
    | .ok (package,core) =>
      let canonicalPath := outputDirectory ++ "/canonical.bendtt"
      IO.FS.writeBinFile canonicalPath ⟨core.bytes.toArray⟩
      let result := Minidregg.Host.BendMemberFrontendCheck.description package core coreEntry canonicalPath packagePath
      IO.FS.writeFile (outputDirectory ++ "/checked.json") (result.compress ++ "\n")
      return (0 : UInt32)
  catch error => IO.eprintln error.toString; return (2 : UInt32)
