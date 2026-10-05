/- Objective source package and publication authoring.

`publication` publishes a package this Host's own front end lowers: the package
names `ObjectiveBendFrontEndIdentity.identity`, and its typed core is
`ObjectiveBendPublication.publishedCore` of the package, the same function the
receiver recomputes at admission. `author` is the ordinary source publication
payload author; its expectedCore is a consumer's own replay (for a third
party's offered core, `ObjectiveBendPublication.publishedCore` again). No
authority is created by source publication. -/
import Compiler.ObjectiveSourcePackage
import Compiler.ObjectiveBendPublication
import Compiler.ObjectiveBendSourceArtifact
import Kernel.ObjectiveBendNativeInput
import Kernel.ObjectiveBendPublishedPackage
import Kernel.ObjectiveBendNativeAdmission
import Compiler.ObjectiveBendGenericResult
import Kernel.ObjectiveActivity
import Kernel.SeatStore
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

/-- A registered output codec by name. -/
def outputCodecOf : String → Except String Digest
  | "scalar" => pure ObjectiveBendPlanAdapter.codecId
  | "result" => pure ObjectiveBendResultAdapter.codecId
  | "combined" => pure Minidregg.Kernel.ObjectiveBendNativeAdmission.combinedCodec
  | "generic" => pure ObjectiveBendGenericResult.codecId
  | "activity" => pure Minidregg.Kernel.ObjectiveActivity.codecId
  | "seat" => pure Minidregg.Kernel.SeatStore.contractCodecId
  | other => throw s!"unknown output codec {other}"

structure Publication where
  package : List UInt8
  artifact : List UInt8
  core : List UInt8
  json : Json

/-- The package of captured modules, naming this Host's front end. -/
def packageOf (modules : List (ObjectiveBendFrontEnd.SourceModule × List UInt8)) (entryModule : Nat)
    (entryDefinition : String) : Minidregg.Compiler.ObjectiveSourcePackage.Package :=
  ⟨ObjectiveBendFrontEndIdentity.identity, modules.map (fun (m, bytes) => ⟨m.name, bytes,
    m.imports.map fun i => ⟨i.importAlias, i.path, i.target⟩⟩), entryModule, entryDefinition⟩

/-- The signer's own publication: the package and the typed core this Host's front end
computes from it (`publishedCore`), paired by `author` as offered and expected core. -/
def publication (package : Minidregg.Compiler.ObjectiveSourcePackage.Package) (outputCodec : String) :
    Except String Publication := do
  if package.frontEnd != ObjectiveBendFrontEndIdentity.identity then
    throw "a publication names this Host's front end"
  if !Minidregg.Compiler.ObjectiveSourcePackage.wellFormed package then
    throw "Objective source package structure/import/pin refusal"
  let core ← match ObjectiveBendPublication.publishedCore package with
    | .ok core => pure core
    | .error d => throw (d.stage ++ ": " ++ d.message)
  let packageBytes := Minidregg.Compiler.ObjectiveSourcePackage.encode package
  let codec ← outputCodecOf outputCodec
  let json ← author packageBytes packageBytes core core (digestStream.encode codec)
  let some declaration := Minidregg.Compiler.ObjectiveSourcePackage.selectedDeclaration package
    | throw "Objective selected declaration missing"
  let artifact : Artifact := ⟨Minidregg.Compiler.ObjectiveSourcePackage.identity package,declaration,core,
    Minidregg.Kernel.ObjectiveBendNativeInput.codecId,codec⟩
  pure ⟨packageBytes,encode artifact,core,json⟩
end Minidregg.Host.ObjectivePackageAuthor
