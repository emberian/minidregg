/- Objective source package and publication authoring.

`load` turns a package-input JSON (exact module source and AST bytes, import
locks, the parser/frontend/elaborator pins) into the canonical package;
`author` is the ordinary source publication payload author. expectedCore comes from the
signing consumer's independent pinned replay of the immutable package bytes.
This module checks exact pairing; supplying that trusted replay is an external
obligation, not a theorem inferred from arbitrary input JSON. No authority is
created by source publication. -/
import Compiler.ObjectiveSourcePackage
import Compiler.ObjectiveBendSourceArtifact
import Kernel.ObjectiveBendNativeInput
import Kernel.ObjectiveBendPublishedPackage
import Kernel.ObjectiveBendNativeAdmission
import Compiler.ObjectiveBendGenericResult
namespace Minidregg.Host.ObjectivePackageAuthor
open Minidregg.Compiler
open Lean Minidregg.Theory Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.ObjectiveBendSourceArtifact
set_option autoImplicit false
private def hex (bytes : List UInt8) : String := String.ofList <| bytes.flatMap fun b =>
  let chars := "0123456789abcdef".toList
  [chars[b.toNat/16]!,chars[b.toNat%16]!]
private def decimal (digest : Digest) : Json := toJson (toString digest.value)
private def atom (id schema : Digest) (bytes : List UInt8) : Json := Json.mkObj [
  ("type",toJson "createAtom"),("atom",decimal id),
  ("kind",Json.mkObj [("type",toJson "inlineObject"),("schema",decimal schema)]),
  ("payload",toJson (hex bytes))]

/-- The receiver's package schema, never a local copy of its derivation. -/
abbrev packageSchema : Digest := Minidregg.Kernel.ObjectiveBendPublishedPackage.schema

def author (packageBytes replayedPackage offeredCore expectedCore outputCodecBytes : List UInt8) : Except String Json := do
  if packageBytes.length > 12582912 || offeredCore.length > 4194304 || expectedCore.length > 4194304 || outputCodecBytes.length > 1024 then throw "source publication byte capacity"
  let some package := Minidregg.Compiler.ObjectiveSourcePackage.decode packageBytes | throw "canonical Objective package required"
  if !Minidregg.Compiler.ObjectiveSourcePackage.wellFormed package then throw "Objective package structure/import/pin refusal"
  let some declaration := Minidregg.Compiler.ObjectiveSourcePackage.selectedDeclaration package | throw "Objective selected declaration missing"
  if packageBytes != replayedPackage then throw "immutable package differs from pinned source/parser replay"
  if offeredCore != expectedCore then throw "offered callable differs from independent immutable-package replay"
  let packet ← parsePacket 4194304 expectedCore
  if (← packet.getObjValAs? String "sourceEntry") != declaration then throw "package/callable selected declaration mismatch"
  let some outputCodec := digestStream.toLawful.decode outputCodecBytes | throw "native output codec encoding required"
  if digestStream.encode outputCodec != outputCodecBytes then throw "noncanonical native output codec"
  let artifact : Artifact := ⟨Minidregg.Compiler.ObjectiveSourcePackage.identity package,
    declaration,offeredCore,Minidregg.Kernel.ObjectiveBendNativeInput.codecId,outputCodec⟩
  let checked ← checkWithin artifact 4194304 16384
  match checked.typed.type with
  | .arrow .. => pure ()
  | _ => throw "unapplied checked callable required"
  match checked.packet.source.term with
  | .get _ name => if name != declaration then throw "actual selected core member mismatch"
  | _ => throw "selected module knot required"
  let artifactBytes := encode artifact
  pure <| Json.mkObj [
    ("schema",toJson "dregg.objective-bend.publication-author.v1"),
    ("packageId",decimal artifact.package),("artifactId",decimal (identity artifact)),
    ("sourceEntry",toJson declaration),("inputCodec",decimal artifact.inputCodec),("outputCodec",decimal artifact.outputCodec),
    ("payload",Json.mkObj [("type",toJson "content"),("actions",toJson ([
      atom artifact.package packageSchema packageBytes,
      atom (identity artifact) schema artifactBytes] : List Json))]),
    ("authority",toJson "none; ordinary current-authorized content proposal required"),
    ("sourceCorrespondence",toJson "exact offered/independently replayed packet; trusted replay supplied by signing consumer"),
    ("laws",toJson "undischarged")]

private def text (j : Json) (k : String) : Except String String := j.getObjValAs? String k
private def rows (j : Json) (k : String) : Except String (Array Json) := do (← j.getObjVal? k).getArr?
private def smallNat (j : Json) (k : String) : Except String Nat := do
  let s ← text j k
  if s.length > 3 then throw "package index textual capacity"
  let some n := s.toNat? | throw "package index decimal"
  if toString n != s then throw "package index noncanonical"
  pure n
private def bytesOf (j : Json) (k : String) : Except String (List UInt8) := do
  let value ← text j k
  if value.length > 16777216 then throw "package hex byte capacity"
  let some bytes := ObjectiveBendPlanAdapter.unhex value.toList | throw s!"{k} must be lowercase hex"
  pure bytes

/-- Package input (schema dregg.objective-bend.source-package-input.v2): exact
module bytes, ASTs, import locks, entry, and the three tool pins. Refuses any
package that is not `wellFormed`. -/
def load (json : Json) : Except String Minidregg.Compiler.ObjectiveSourcePackage.Package := do
  if (← text json "schema") != "dregg.objective-bend.source-package-input.v2" then throw "Objective package input schema"
  if (← text json "edition") != "objective-bend-1" then throw "Objective source edition"
  let raw ← rows json "modules"
  if raw.isEmpty || raw.size > 64 then throw "Objective module capacity"
  let modules ← raw.toList.mapM fun m => do
    let imports ← (← rows m "imports").toList.mapM fun i => do
      pure ({importAlias := ← text i "alias", path := ← text i "path", target := ← smallNat i "target"} :
        Minidregg.Compiler.ObjectiveSourcePackage.Import)
    pure ({name := ← text m "name", source := ← bytesOf m "sourceHex", ast := ← bytesOf m "astHex", imports} :
      Minidregg.Compiler.ObjectiveSourcePackage.Module)
  if (modules.map (fun m => m.source.length)).sum > 4194304 ||
      (modules.map (fun m => m.ast.length)).sum > 8388608 then throw "Objective source/AST byte capacity"
  let package : Minidregg.Compiler.ObjectiveSourcePackage.Package :=
    ⟨← text json "parserSha256",← text json "frontendSha256",← text json "elaboratorSha256",modules,
      ← smallNat json "entryModule",← text json "entryDefinition"⟩
  if !Minidregg.Compiler.ObjectiveSourcePackage.wellFormed package then
    throw "Objective source package structure/import/pin refusal"
  pure package

/-- A registered output codec by name. -/
def outputCodecOf : String → Except String Digest
  | "scalar" => pure ObjectiveBendPlanAdapter.codecId
  | "result" => pure ObjectiveBendResultAdapter.codecId
  | "combined" => pure Minidregg.Kernel.ObjectiveBendNativeAdmission.combinedCodec
  | "generic" => pure ObjectiveBendGenericResult.codecId
  | other => throw s!"unknown output codec {other}"

structure Publication where
  package : List UInt8
  artifact : List UInt8
  core : List UInt8
  json : Json

/-- The signer's own publication: the package from its input, the typed core
its pinned elaborator just produced (canonicalized, never re-elaborated here),
and the payload `author` checks. Offered and expected core are the same bytes
because this signer is the replaying consumer; a third party's offered core
goes through `author` with the consumer's own replay instead. -/
def publication (input core : List UInt8) (outputCodec : String) : Except String Publication := do
  let some text := String.fromUTF8? ⟨input.toArray⟩ | throw "package input is not UTF-8"
  let package ← load (← Json.parse text)
  let packageBytes := Minidregg.Compiler.ObjectiveSourcePackage.encode package
  let canonical ← canonicalizePacket 4194304 core
  let codec ← outputCodecOf outputCodec
  let json ← author packageBytes packageBytes canonical canonical (digestStream.encode codec)
  let some declaration := Minidregg.Compiler.ObjectiveSourcePackage.selectedDeclaration package
    | throw "Objective selected declaration missing"
  let artifact : Artifact := ⟨Minidregg.Compiler.ObjectiveSourcePackage.identity package,declaration,canonical,
    Minidregg.Kernel.ObjectiveBendNativeInput.codecId,codec⟩
  pure ⟨packageBytes,encode artifact,canonical,json⟩
end Minidregg.Host.ObjectivePackageAuthor
