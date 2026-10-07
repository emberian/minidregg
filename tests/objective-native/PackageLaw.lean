/- A package's `law` declarations travel from source to the object kernel's judgment
(`lake env lean --run tests/objective-native/PackageLaw.lean tests/objective-native/CappedTally.obend tally`).

1. The package published from the source carries exactly the laws of its entry module, as the
   front end reads them: `Kernel.ObjectLawEnforced.cappedLaws` (the laws the kernel teeth
   `capped_tally_teeth` are stated over).
2. The activity kernel's `replayPackage` accepts the honest pair (the receiver recomputes the laws).
3. The same artifact with the `cap` law's bound changed to 1001 (so another pin) is refused as
   `packageReplay`: the receiver's replay of the source disagrees.
4. An object pinned to the package, judged with the laws the artifact carries: an honest write
   (5 -> 7) is admitted, a write past the cap (5 -> 1001) is refused naming the `cap` clause, a
   write lowering the total (7 -> 5) is refused naming the `grows` clause.
5. A declared state type without `total` is refused at creation naming `total`.
Prints `PACKAGE LAW PASS` and exits 0 only if every row holds. -/
import Host.ObjectivePackageAuthor
import Host.ObjectiveBendFrontEnd
import Kernel.ObjectLawEnforced
open Lean Minidregg
open Minidregg.Kernel.ObjectiveActivity (Config Stored Refusal replayPackage encodeStored)
open Minidregg.Kernel.ObjectLawEnforced (cappedLaws cappedRecord tallyAt writeFacts tallyType)
open Minidregg.Kernel.ObjectRecord (admitWrite leafOf accepted lawFieldIssue)

def config : Config :=
  { deployment := ⟨⟨0⟩, 1, 2, 3⟩, asset := 0, collector := 4, limits := ⟨100000, 100000⟩,
    planBudget := { nodes := 20000, ticks := 100000, bytes := 200000 }, maxTicks := 100000,
    maxPatience := 1000, typeFuel := 16384, maxArtifactBytes := 4194304,
    tariff := Minidregg.Kernel.ObjectiveTariff.Tariff.unit, abandonGrace := 16, storageRate := 1 }

def main (args : List String) : IO UInt32 := do
  let [sourcePath, entry] := args | IO.eprintln "usage: SOURCE.obend ENTRY"; return 2
  let bytes ← IO.FS.readBinFile sourcePath
  let fail (why : String) : IO UInt32 := do IO.eprintln ("PACKAGE LAW FAIL: " ++ why); return 1
  let module ← match ← (Host.ObjectiveBendFrontEnd.captureModule #[] "CappedTally" bytes none [] false).run with
    | .ok (m, _) => pure m
    | .error d => return ← fail d.json.compress
  let package := Host.ObjectivePackageAuthor.packageOf [(module, bytes.toList)] 0 entry
  let published ← match Host.ObjectivePackageAuthor.publication package "activity" with
    | .ok p => pure p
    | .error e => return ← fail ("publication: " ++ e)
  let some artifact := Compiler.ObjectiveBendSourceArtifact.decode published.artifact
    | return ← fail "artifact does not decode"
  -- 1. the artifact carries the source's laws
  if artifact.laws != cappedLaws then
    return ← fail ("the artifact's laws are not the source's: " ++ reprStr artifact.laws)
  -- 2. the receiver replays them
  let stored : Stored := ⟨published.artifact, published.package, 9⟩
  let pin := Compiler.ObjectiveBendSourceArtifact.identity artifact
  if let .error r := replayPackage config stored pin then
    return ← fail ("honest pair refused: " ++ reprStr r)
  -- 3. a tampered law is refused by the replay
  let tampered := { artifact with laws := [("cap", .leC (.field "total") 1001), ("grows", .monotone "total")] }
  let forged : Stored := ⟨Compiler.ObjectiveBendSourceArtifact.encode tampered, published.package, 9⟩
  match replayPackage config forged (Compiler.ObjectiveBendSourceArtifact.identity tampered) with
  | .ok _ => return ← fail "a tampered law was accepted"
  | .error (.packageReplay _) => pure ()
  | .error r => return ← fail ("a tampered law was refused for another reason: " ++ reprStr r)
  -- 4. the kernel judges writes by the artifact's laws
  let record := cappedRecord artifact.laws
  if !accepted (admitWrite record writeFacts (some (tallyAt 5)) (tallyAt 7)) then
    return ← fail "an honest write was refused"
  if leafOf (admitWrite record writeFacts (some (tallyAt 5)) (tallyAt 1001)) !=
      some ⟨[1, 0], .le "state/total" 1000, some 5, some 1001⟩ then
    return ← fail "a write past the cap was not refused at the cap law"
  if leafOf (admitWrite record writeFacts (some (tallyAt 7)) (tallyAt 5)) !=
      some ⟨[1, 1], .monotone "state/total", some 7, some 5⟩ then
    return ← fail "a lowering write was not refused at the grows law"
  -- 5. a state type without the field
  if lawFieldIssue (.field "count" .natural .emptyRow) artifact.laws != some "total" then
    return ← fail "a state type without `total` was not refused naming it"
  if lawFieldIssue tallyType artifact.laws != none then
    return ← fail "the tally's own state type was refused"
  IO.println ("PACKAGE LAW PASS: the artifact carries " ++ toString artifact.laws.length ++
    " laws (cap, grows), replayed from source; a tampered law is refused; past-cap and lowering writes " ++
    "are refused naming their law; a state type without `total` is refused naming it")
  return 0
