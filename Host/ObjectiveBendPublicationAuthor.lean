/- Canonical publication material for ordinary Objective Bend source objects.
This producer checks the exact reflected closure and composed Book. It emits
ordinary content actions and a compact native world-kind definition after the
caller supplies the actually published source root. It grants no authority;
the current signed native receiving and reference loader remain mandatory. -/
import Compiler.ObjectiveBendReference
import Kernel.ObjectiveBendInstanceLoader
import Lean

namespace Minidregg.Host.ObjectiveBendPublicationAuthor
open Minidregg.Compiler
open Minidregg.Compiler.ObjectiveBendReference
open Minidregg.Theory.BendTT
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

private def checkedIO {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def hexByte (byte : UInt8) : String :=
  let digits := "0123456789abcdef".toList.toArray
  String.ofList [digits[byte.toNat / 16]!, digits[byte.toNat % 16]!]

private def hex (bytes : List UInt8) : String :=
  String.join (bytes.map hexByte)

private def decimal (value : Nat) : Lean.Json := .str (toString value)

structure Material where
  partials : List ObjectiveBendPrototype.Partial
  core : Core
  closure : ObjectiveBendInstance.Pin
  loaded : ObjectiveBendInstance.Loaded closure
  partialsExact : closure.prototypes = partials
  coreExact : closure.core = core.book
  identitiesExact : core.partials = partials.map partialDigest

private def readMaterial (directory caseName : String) : IO Material := do
  let count ← match caseName with
    | "complete" => pure 5
    | "alternate" => pure 6
    | _ => throw (IO.userError "case must be complete or alternate")
  let partials ← (List.range count).mapM fun index => do
    let raw ← IO.FS.readBinFile (directory ++ "/partial-" ++ toString (index + 1) ++ ".bin")
    match ObjectiveBendPrototype.decode raw.toList with
    | none => throw (IO.userError "noncanonical Partial publication")
    | some prototype => pure prototype
  let raw ← IO.FS.readBinFile (directory ++ "/" ++ caseName ++ ".bendtt")
  let coreAdmission ← checkedIO (BendCoreAdmission.admit raw.toList)
  let specs ← checkedIO (partials.mapM ObjectiveBendPrototype.reflect)
  let generated := (ObjectiveBendLinker.generated specs).map Def.k
  let helpers := coreAdmission.book.filter fun definition => !generated.contains definition.k
  let closure : ObjectiveBendInstance.Pin := ⟨partials, raw.toList⟩
  let loaded ← checkedIO (Kernel.ObjectiveBendInstanceLoader.loadPin helpers closure)
  let core : Core := ⟨partials.map partialDigest, raw.toList⟩
  pure ⟨partials, core, closure, loaded, rfl, rfl, rfl⟩

private def atom (identity schema : Digest) (bytes : List UInt8) : Lean.Json :=
  .mkObj [("type", .str "createAtom"), ("atom", decimal identity.value),
    ("kind", .mkObj [("type", .str "inlineObject"), ("schema", decimal schema.value)]),
    ("payload", .str (hex bytes))]

def sourcePayload (material : Material) : Lean.Json :=
  let partialActions := material.partials.map fun prototype =>
    atom (partialDigest prototype) partialSchema (ObjectiveBendPrototype.encode prototype)
  .mkObj [("type", .str "content"),
    ("actions", .arr (partialActions ++
      [atom (coreIdentity material.core) coreSchema (encodeCore material.core)]).toArray)]

def pin (material : Material) (resource : Nat) (root : Digest) : Pin :=
  ⟨material.partials.map (fun prototype => ⟨resource, root, partialDigest prototype⟩),
    ⟨resource, root, coreIdentity material.core⟩⟩

theorem pin_matches (material : Material) (resource : Nat) (root : Digest) :
    Matches (pin material resource root) material.partials material.core := by
  refine ⟨?_, rfl, material.identitiesExact⟩
  simp [pin]

/-- A source-neutral native kind: one immutable compact behavior pin and three
heterogeneous useful state fields. Member UI may author another descriptor;
the loader recognizes semantic meaning, not this helper's names or positions. -/
def definition (pinValue : Pin) : Lean.Json :=
  .mkObj [("descriptor", .mkObj [("revision", .str "1"), ("fields", .arr #[
    .mkObj [("id", .str "0"), ("name", .str "prototype"), ("meaning", .str ObjectiveBendInstance.pinMeaning),
      ("codec", .str "bytes"), ("discipline", .str "rom")],
    .mkObj [("id", .str "1"), ("name", .str "candidateRevision"), ("meaning", .str "workshop candidate revision"),
      ("codec", .str "nat"), ("discipline", .str "ram")],
    .mkObj [("id", .str "2"), ("name", .str "reviewBalance"), ("meaning", .str "workshop review accounting"),
      ("codec", .str "int"), ("discipline", .str "ram")],
    .mkObj [("id", .str "3"), ("name", .str "title"), ("meaning", .str "workshop title"),
      ("codec", .str "bytes"), ("discipline", .str "ram")]])]),
    ("defaults", .arr #[
      .mkObj [("field", .str "0"), ("key", .str "0"), ("value", .str (hex (encode pinValue)))],
      .mkObj [("field", .str "1"), ("key", .str "0"), ("value", .str "1")],
      .mkObj [("field", .str "2"), ("key", .str "0"), ("value", .str "0")],
      .mkObj [("field", .str "3"), ("key", .str "0"), ("value", .str (hex "Community workshop".toUTF8.toList))]])]

def run (args : List String) : IO UInt32 := do
  match args with
  | ["source", directory, caseName, output] =>
    IO.FS.createDirAll output
    let material ← readMaterial directory caseName
    IO.FS.writeBinFile (output ++ "/core.bin") ⟨(encodeCore material.core).toArray⟩
    IO.FS.writeFile (output ++ "/source-payload.json") (sourcePayload material).pretty
    IO.FS.writeFile (output ++ "/source-identities.json") (Lean.Json.mkObj [
      ("partials", .arr (material.partials.map (fun prototype => decimal (partialDigest prototype).value)).toArray),
      ("core", decimal (coreIdentity material.core).value), ("coreSchema", decimal coreSchema.value),
      ("partialSchema", decimal partialSchema.value),
      ("prototype", decimal material.loaded.construction.root.id)]).pretty
    IO.println "SOURCE MATERIAL PASS: exact reflected construction; ordinary native admission still required"
    pure 0
  | ["pin", directory, caseName, resourceText, rootText, output] =>
    let some resource := resourceText.toNat? | throw (IO.userError "resource must be decimal")
    let some root := rootText.toNat? | throw (IO.userError "published root must be decimal")
    IO.FS.createDirAll output
    let material ← readMaterial directory caseName
    let pinned := pin material resource ⟨root⟩
    IO.FS.writeBinFile (output ++ "/pin.bin") ⟨(encode pinned).toArray⟩
    IO.FS.writeFile (output ++ "/definition.json") (definition pinned).pretty
    IO.println ("COMPACT PIN MATERIAL PASS bytes=" ++ toString (encode pinned).length ++
      "; actual published root is checked by native source loader")
    pure 0
  | _ => throw (IO.userError "usage: source DIR complete|alternate OUT; pin DIR CASE RESOURCE ROOT OUT")

#assert_axioms pin_matches

end Minidregg.Host.ObjectiveBendPublicationAuthor

def main (args : List String) : IO UInt32 :=
  Minidregg.Host.ObjectiveBendPublicationAuthor.run args
