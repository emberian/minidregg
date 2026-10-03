/- Scoped source/codec receiving check. The input is an emitted complete helper
Book, checked by BendCoreAdmission. This exercise does not install a source,
create a world identity, or claim accepted invocation/action authority. -/
import Host.BendSurfaceJson

namespace Minidregg.Host.BendSurfaceSmoke
open Minidregg.Compiler
open Minidregg.Compiler.BendWorldSurface
open Minidregg.Compiler.BendSurfaceLowering
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.BendTT
abbrev BTerm := Minidregg.Theory.BendTT.Term
set_option autoImplicit false

private def application (entry : String) (arguments : List BTerm) : BTerm :=
  arguments.foldl (fun function argument => .App .Q1 function argument) (.Ref entry)
private def nativeIntent (name : String) : Intent := ⟨⟨42⟩, name, ⟨2⟩, 3, ⟨4⟩, [0]⟩

private def sourceFace : Surface := ⟨⟨42⟩, "source",
  [⟨2, 0, "Source", []⟩, ⟨1, 1, "Activity", []⟩, ⟨4, 0, "Workshop", [0, 1]⟩], 2, []⟩
private def domainFace : Surface := ⟨⟨42⟩, "domain",
  [⟨2, 0, "Catalog", []⟩, ⟨1, 1, "Capacity", []⟩, ⟨1, 2, "Review", []⟩,
   ⟨3, 0, "Request review", []⟩, ⟨3, 1, "Adopt", []⟩,
   ⟨4, 0, "Workshop", [0, 1, 2, 3, 4]⟩], 5,
  [nativeIntent "requestReview", nativeIntent "proposeAdoption"]⟩

private def checkFace (core : BendCoreAdmission.Checked) (entry : String)
    (arguments : List BTerm) (expected : Surface) (observations : Nat) : IO Unit := do
  let some result := execute core 20000 20000 (application entry arguments)
      expected.artifact expected.exportName observations
    | throw (IO.userError ("Surface execution/decoding refused " ++ entry))
  unless result.surface = expected do throw (IO.userError ("Surface result differs " ++ entry))
  unless (Minidregg.Host.BendSurfaceJson.evaluated result).compress =
      (Minidregg.Host.BendSurfaceJson.surface expected).compress do
    throw (IO.userError "typed JSON projection differs")
  IO.println ("SURFACE SOURCE CHECK PASS " ++ entry ++ " steps=" ++ toString result.count)
  IO.println (Minidregg.Host.BendSurfaceJson.evaluated result).compress

private def refuseMalformed : IO Unit := do
  let badBytes := constructor "WorldSurface.Surface"
    [digestTerm ⟨42⟩, BendSourceRepresentation.natListTerm [256],
     listTerm nodeTerm sourceFace.nodes, BendSourceRepresentation.natTerm sourceFace.root,
     listTerm intentTerm sourceFace.intents]
  unless lower badBytes = none do throw (IO.userError "out-of-range byte admitted")
  let badUtf8 := constructor "WorldSurface.Surface"
    [digestTerm ⟨42⟩, BendSourceRepresentation.bytesTerm [255],
     listTerm nodeTerm sourceFace.nodes, BendSourceRepresentation.natTerm sourceFace.root,
     listTerm intentTerm sourceFace.intents]
  unless lower badUtf8 = none do throw (IO.userError "invalid UTF8 admitted")
  unless lower (sourceTerm { sourceFace with exportName := String.singleton (Char.ofNat 0) }) = none do
    throw (IO.userError "NUL export admitted")
  let forward := { sourceFace with nodes := [⟨4, 0, "Forward", [0]⟩], root := 0 }
  unless bounded forward 2 = false do throw (IO.userError "forward/cycle node admitted")
  IO.println "SURFACE MALFORMED CHECK PASS byte/UTF8/NUL/backwards"

#assert_axioms Minidregg.Compiler.BendSurfaceLowering.lower_exact
#assert_axioms Minidregg.Compiler.BendSurfaceLowering.abi_definition_exact
#assert_axioms Minidregg.Compiler.BendSurfaceLowering.evaluated_source_exact
#assert_axioms Minidregg.Compiler.BendSurfaceLowering.evaluated_origin_exact

end Minidregg.Host.BendSurfaceSmoke

open Minidregg.Compiler.BendSurfaceLowering
open Minidregg.Compiler.BendSourceRepresentation
open Minidregg.Host.BendSurfaceSmoke

def main (arguments : List String) : IO Unit := do
  let [bookPath] := arguments | throw (IO.userError "usage: BendSurfaceSmoke emitted-complete-book")
  let bytes ← IO.FS.readBinFile bookPath
  let core ← match Minidregg.Compiler.BendCoreAdmission.canonicalize bytes.toList with
    | .error why => throw (IO.userError why)
    | .ok value => pure value
  checkFace core "WorkshopFaces.source_face"
      [digestTerm ⟨42⟩, stringTerm "source", stringTerm "Source", stringTerm "Activity",
       stringTerm "Workshop", natTerm 0, natTerm 1, listTerm intentTerm []] sourceFace 2
  checkFace core "WorkshopFaces.domain_face"
      [digestTerm ⟨42⟩, stringTerm "domain", stringTerm "Workshop", stringTerm "Catalog",
       stringTerm "Capacity", stringTerm "Review", stringTerm "Request review", stringTerm "Adopt",
       natTerm 0, natTerm 1, natTerm 2, intentTerm (nativeIntent "requestReview"),
       intentTerm (nativeIntent "proposeAdoption")] domainFace 3
  refuseMalformed
  IO.println "SURFACE ACTUAL HELPER-BOOK RECEIVING PASS"
