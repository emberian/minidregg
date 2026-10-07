/- The activity kernel publishes an artifact WITH its source package and replays the front end
(`lake env lean --run tests/objective-native/ActivityReplay.lean world/activity/Tally.obend tally`).

0. The honest pair: the package names this front end, the artifact's typed core is the
   package's `publishedCore`, output codec `ObjectiveActivity.codecId`.
1. `replayPackage` accepts the honest pair, and `loadProgram` builds the activity program
   from the stored cell body with a typed `Start` input: the program applies the replay's
   erased term (`Program.runs_front_end_output`).
2. A foreign core: the same package with an artifact whose typed core has one byte changed
   (so another pin) is refused as `packageReplay`.
3. A foreign front end: the package re-pinned to another front end is refused as
   `packageSource` (the artifact is re-pinned to it, so this is not an identity refusal).
4. No package: the artifact alone (empty package bytes) is refused as `packageSource`.
5. A package of another source (one comment line added) under the honest artifact is
   refused as `packageSource` (the artifact names another package).
Prints `ACTIVITY REPLAY PASS` and exits 0 only if every row holds. -/
import Host.ObjectivePackageAuthor
import Host.ObjectiveBendFrontEnd
import Kernel.ObjectiveActivity
open Lean Minidregg
open Minidregg.Kernel.ObjectiveActivity (Config Stored Refusal replayPackage loadProgram encodeStored codecId)

def config : Config :=
  { deployment := ⟨⟨0⟩, 1, 2, 3⟩, asset := 0, collector := 4, limits := ⟨100000, 100000⟩,
    planBudget := { nodes := 20000, ticks := 100000, bytes := 200000 }, maxTicks := 100000, maxExtractTicks := 1600000,
    maxPatience := 1000, typeFuel := 16384, maxArtifactBytes := 4194304,
    tariff := Minidregg.Kernel.ObjectiveTariff.Tariff.unit, abandonGrace := 16, storageRate := 1 }

def refusalKind : Refusal → String
  | .packageReplay _ => "packageReplay"
  | .packageSource _ => "packageSource"
  | .packageIdentity => "packageIdentity"
  | .packageMissing => "packageMissing"
  | .packageType _ => "packageType"
  | _ => "other"

def main (args : List String) : IO UInt32 := do
  let [sourcePath, entry] := args | IO.eprintln "usage: SOURCE.obend ENTRY"; return 2
  let bytes ← IO.FS.readBinFile sourcePath
  let fail (why : String) : IO UInt32 := do IO.eprintln ("ACTIVITY REPLAY FAIL: " ++ why); return 1
  let module ← match ← (Host.ObjectiveBendFrontEnd.captureModule #[] "Activity" bytes none [] false).run with
    | .ok (m, _) => pure m
    | .error d => return ← fail d.json.compress
  let package := Host.ObjectivePackageAuthor.packageOf [(module, bytes.toList)] 0 entry
  let some declaration := Compiler.ObjectiveSourcePackage.selectedDeclaration package
    | return ← fail "no selected declaration"
  let core ← match Compiler.ObjectiveBendPublication.publishedCore package with
    | .ok core => pure core
    | .error d => return ← fail ("publishedCore: " ++ d.message)
  let artifactOf (p : Compiler.ObjectiveSourcePackage.Package) (core : List UInt8) :
      Compiler.ObjectiveBendSourceArtifact.Artifact :=
    ⟨Compiler.ObjectiveSourcePackage.identity p, declaration, core, Kernel.ObjectiveBendNativeInput.codecId, codecId,
      ((Compiler.ObjectiveBendPublication.publishedLaws p).toOption.getD [])⟩
  let pairOf (p : Compiler.ObjectiveSourcePackage.Package) (a : Compiler.ObjectiveBendSourceArtifact.Artifact) : Stored :=
    ⟨Compiler.ObjectiveBendSourceArtifact.encode a, Compiler.ObjectiveSourcePackage.encode p, 9⟩
  let refuses (label kind : String) (stored : Stored) (a : Compiler.ObjectiveBendSourceArtifact.Artifact) :
      IO (Option String) := do
    match replayPackage config stored (Compiler.ObjectiveBendSourceArtifact.identity a) with
    | .ok _ => return some (label ++ ": accepted")
    | .error r => return if refusalKind r == kind then none else some (label ++ ": refused as " ++ refusalKind r)
  -- 0/1. honest
  let honest := artifactOf package core
  let stored := pairOf package honest
  let pin := Compiler.ObjectiveBendSourceArtifact.identity honest
  match replayPackage config stored pin with
  | .error r => return ← fail ("honest pair refused: " ++ refusalKind r)
  | .ok _ => pure ()
  let input : Theory.ObjectiveBendDemandData.Data :=
    .record [("init", .variant "set" (.natural 5)), ("decider", .natural 7)]
  match loadProgram config (encodeStored stored) pin input with
  | .error r => return ← fail ("honest program refused: " ++ refusalKind r)
  | .ok _ => pure ()
  -- 2. foreign core
  let some last := core.getLast? | return ← fail "empty core"
  let foreignCore := artifactOf package (core.dropLast ++ [last ^^^ 1])
  if let some why ← refuses "foreign core" "packageReplay" (pairOf package foreignCore) foreignCore then return ← fail why
  -- 3. foreign front end
  let foreignPackage := { package with frontEnd := Compiler.Sha256.hexString "another front end" }
  let foreignPinned := artifactOf foreignPackage core
  if let some why ← refuses "foreign front end" "packageSource" (pairOf foreignPackage foreignPinned) foreignPinned then
    return ← fail why
  -- 4. no package
  if let some why ← refuses "no package" "packageSource" ⟨Compiler.ObjectiveBendSourceArtifact.encode honest, [], 9⟩ honest then
    return ← fail why
  -- 5. another source under the honest artifact
  let moved := { package with modules := [⟨"Activity", bytes.toList ++ "# one more comment line\n".toUTF8.toList, []⟩] }
  if let some why ← refuses "another source" "packageSource" (pairOf moved honest) honest then return ← fail why
  IO.println ("ACTIVITY REPLAY PASS: " ++ toString core.length ++ "-byte core replayed from the stored package; " ++
    "program loaded; foreign core, foreign front end, missing package and another source refused")
  return 0
