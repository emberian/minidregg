/-
Pinned native verification and full-prefix disclosure-intent source preparation
against the durable real grain R fixture. This is a read-only probe; it does
not sign, post, relay, or mutate a Mini Store.
-/
import Host.Main
import Host.GrainOriginPreparation

namespace GrainOriginPreparationProbe

open Minidregg.Compiler
open Minidregg.Host.GrainOriginPreparation

def run : IO Unit := do
  let root := "/Users/ember/dev/minidregg/docs/evidence/2026-09-26-hermes-grain-origin/"
  let settings ← Minidregg.Host.loadSettings (System.FilePath.mk (root ++ "origin-pin-mac.json"))
  let packageBytes := (← IO.FS.readBinFile (root ++ "7003-package.bin")).toList
  let expectedSource := (← IO.FS.readBinFile (root ++ "R.source")).toList
  let context := Minidregg.Host.GrainOriginSource.ArticleContext.application
    "fn.test" "Sat, 26 Sep 2026 09:45:00 +0000"
  let selection : Minidregg.Host.GrainOriginSource.Selection := ⟨7102, 7101, 7003⟩
  let intent : DisclosureIntent :=
    ⟨true, "fn.test", "Full Mini genesis and accepted prefix may reach fn peers and readers"⟩
  let .ok prepared ← prepareForDisclosure settings.config packageBytes context selection intent
    | throw (IO.userError "independent pinned native verification or rendering refused real R")
  unless ResourceBirthCodec.bytesEqual prepared.rendered.source expectedSource &&
      prepared.scope.acceptedCount == 10 &&
      prepared.scope.packageLength == packageBytes.length &&
      prepared.scope.packageDigest.length == 32 &&
      prepared.scope.prefixDigest.length == 32 do
    throw (IO.userError "verified source bytes or full-prefix disclosure scope differs")
  let .error _ ← prepareForDisclosure settings.config packageBytes context selection
      { intent with wholePrefixDisclosure := false }
    | throw (IO.userError "missing whole-prefix disclosure intent was admitted")
  let .error _ ← prepareForDisclosure settings.config packageBytes context selection
      { intent with destinationNewsgroup := "fn.private" }
    | throw (IO.userError "destination Newsgroups mismatch was admitted")
  IO.println s!"PASS verified grain R: source={prepared.rendered.source.length}, prefix={prepared.scope.prefixLength}, accepted={prepared.scope.acceptedCount}, packageDigest={Minidregg.Host.Json.encodeHex prepared.scope.packageDigest}, prefixDigest={Minidregg.Host.Json.encodeHex prepared.scope.prefixDigest}; missing/mismatched disclosure intent rejected"

end GrainOriginPreparationProbe

#eval GrainOriginPreparationProbe.run
