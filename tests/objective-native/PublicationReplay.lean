/- Publication and the receiver's replay agree, and the replay refuses what it must
(`lake env lean --run tests/objective-native/PublicationReplay.lean SOURCE.obend ENTRY`).

1. `ObjectivePackageAuthor.publication` of the one-module package names this front end
   and signs `publishedCore`; the receiver's `replayedCore` of the decoded package is
   byte-identical to the artifact's typed core (`SourceSelection.replayExact` holds).
2. The same package naming another front end: `publication` refuses it (and admission's
   `frontEndExact`/`frontEndOwn` would).
3. One source byte changed (a comment): `replayedCore` of that package is a different
   core, so the honest artifact does not pair with it.
4. The artifact's typed core with one byte changed is not what the receiver computes.
5. The same source with a top-level `law cap: new.total <= 1000` publishes an artifact carrying
   exactly that law (a different identity: the identity commits the laws); the receiver's
   `replayAccept` accepts the honest laws and refuses a tampered law (bound 1001) and an
   artifact that drops it, each with "offered laws differ".
Prints `PUBLICATION REPLAY PASS` and exits 0 only if every row holds. -/
import Host.ObjectivePackageAuthor
import Host.ObjectiveBendFrontEnd
open Lean Minidregg

def main (args : List String) : IO UInt32 := do
  let [sourcePath, entry] := args | IO.eprintln "usage: SOURCE.obend ENTRY"; return 2
  let bytes ← IO.FS.readBinFile sourcePath
  let fail (why : String) : IO UInt32 := do IO.eprintln ("PUBLICATION REPLAY FAIL: " ++ why); return 1
  let module ← match ← (Host.ObjectiveBendFrontEnd.captureModule #[] "Method" bytes none [] false).run with
    | .ok (m, _) => pure m
    | .error d => return ← fail d.json.compress
  let package := Host.ObjectivePackageAuthor.packageOf [(module, bytes.toList)] 0 entry
  let some honest := (Host.ObjectivePackageAuthor.publication package "generic").toOption
    | return ← fail "honest publication refused"
  let some decoded := Compiler.ObjectiveSourcePackage.decode honest.package | return ← fail "package does not decode"
  let some artifact := Compiler.ObjectiveBendSourceArtifact.decode honest.artifact | return ← fail "artifact does not decode"
  -- 1. the receiver's replay of the published package IS the published core
  if decoded.frontEnd != Compiler.ObjectiveBendFrontEndIdentity.identity then return ← fail "package names another front end"
  if Compiler.ObjectiveBendPublication.replayedCore decoded != some artifact.typedCore then
    return ← fail "receiver replay differs from the published core"
  -- 2. another front end's pin
  let foreign := { package with frontEnd := Compiler.Sha256.hexString "another front end" }
  if (Host.ObjectivePackageAuthor.publication foreign "generic").toOption.isSome then
    return ← fail "a package naming another front end was published"
  -- 3. one source byte changed
  let changed := bytes.toList ++ "# one more comment line\n".toUTF8.toList
  let moved := { package with modules := [⟨"Method", changed, []⟩] }
  match Compiler.ObjectiveBendPublication.replayedCore moved with
  | some core => if core == artifact.typedCore then return ← fail "changed source replays to the same core"
  | none => return ← fail "changed source no longer lowers"
  -- 4. one core byte changed
  let some last := artifact.typedCore.getLast? | return ← fail "empty core"
  let tampered := artifact.typedCore.dropLast ++ [last ^^^ 1]
  if Compiler.ObjectiveBendPublication.replayedCore decoded == some tampered then
    return ← fail "a tampered core equals the replay"
  -- 5. the enforced laws travel in the artifact and are replayed from source
  if !artifact.laws.isEmpty then return ← fail "a source without laws published laws"
  let lawful := bytes.toList ++ "law cap: new.total <= 1000\n".toUTF8.toList
  let lawPackage := { package with modules := [⟨"Method", lawful, []⟩] }
  let some withLaw := (Host.ObjectivePackageAuthor.publication lawPackage "generic").toOption
    | return ← fail "a package with a law was not published"
  let some lawArtifact := Compiler.ObjectiveBendSourceArtifact.decode withLaw.artifact
    | return ← fail "law artifact does not decode"
  let cap : Compiler.ObjectiveBendLaw.LawExpr := .leC (.field "total") 1000
  if lawArtifact.laws != [("cap", cap)] then return ← fail "the artifact does not carry the source's law"
  if Compiler.ObjectiveBendSourceArtifact.identity lawArtifact == Compiler.ObjectiveBendSourceArtifact.identity artifact then
    return ← fail "the identity does not commit the laws"
  let some lawDecoded := Compiler.ObjectiveSourcePackage.decode withLaw.package | return ← fail "law package does not decode"
  let replayWith (laws : List (String × Compiler.ObjectiveBendLaw.LawExpr)) :=
    Compiler.ObjectiveBendPublication.replayAccept lawDecoded lawArtifact.typedCore laws 16384
  if !(replayWith lawArtifact.laws).toBool then return ← fail "the honest laws were refused"
  for (label, forged) in [("tampered bound", [("cap", Compiler.ObjectiveBendLaw.LawExpr.leC (.field "total") 1001)]),
      ("dropped law", [])] do
    match replayWith forged with
    | .ok _ => return ← fail (label ++ ": accepted")
    | .error d => if d.message != "offered laws differ from the front end's replay of the package" then
        return ← fail (label ++ ": refused for another reason: " ++ d.message)
  IO.println ("PUBLICATION REPLAY PASS: " ++ toString artifact.typedCore.length ++ "-byte core; front end " ++
    Compiler.ObjectiveBendFrontEndIdentity.identity ++ "; foreign pin refused; changed source and tampered core differ; " ++
    "the law travels in the artifact, the identity commits it, a tampered or dropped law is refused")
  return 0
