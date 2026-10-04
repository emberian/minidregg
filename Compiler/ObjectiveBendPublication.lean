/- The typed core a source package publishes is a FUNCTION of the package.

`replay` runs the Lean front end (`ObjectiveBendFrontEnd`) on the package's own
source bytes: decode and fingerprint every module, parse it, lock each parsed
import edge to the module the package says it targets, and lower the selected
declaration in definition mode with the publication type fuel. `publishedCore`
is the canonical bytes of the resulting typed-core packet.

The publisher signs exactly these bytes (`Host.ObjectivePackageAuthor.publication`),
and the receiver recomputes them and admits an artifact only when its typed core
is byte-identical and the package names this front end
(`ObjectiveBendNativeAdmission.SourceSelection.replayExact`). So the package's
`frontEnd` pin is not a label the publisher asserts: it names the computation
the receiver performs. -/
import Compiler.ObjectiveSourcePackage
import Compiler.ObjectiveBendFrontEndIdentity
namespace Minidregg.Compiler.ObjectiveBendPublication
open Lean
open Minidregg.Compiler.ObjectiveBendFrontEnd
set_option autoImplicit false

/-- The checker fuel every published definition carries in its packet. -/
def typeFuel : Nat := 16384

def limits : Json := Json.mkObj [("heap", toJson "100000"), ("stack", toJson "100000"), ("ticks", toJson "100000"),
  ("typeFuel", toJson (toString typeFuel))]

def refusal (message : String) : Diagnostic := { stage := "objective-source-replay", message }

/-- Module `index` of the package, after `prior`: strict UTF-8, parsed, and every parsed import
edge exactly the package's lock (alias, path, an earlier target named by the path). -/
def replayModule (prior : Array SourceModule) (m : ObjectiveSourcePackage.Module) :
    Except Diagnostic (SourceModule × ObjectiveBendElaborate.Module) := do
  let some source := ObjectiveBendParse.decodeSource ⟨m.source.toArray⟩
    | throw (refusal ("module source is not UTF-8: " ++ m.name))
  let ast ← parseSource m.name source
  let edges := ((ast.getObjVal? "imports").bind Json.getArr?).toOption.getD #[]
  if edges.size != m.imports.length then throw (refusal ("import count differs: " ++ m.name))
  let mut imports : List LockedImport := []
  for (edge, lock) in edges.toList.zip m.imports do
    let edgeAlias := (edge.getObjValAs? String "alias").toOption.getD ""
    let edgePath := (edge.getObjValAs? String "path").toOption.getD ""
    if edgeAlias != lock.importAlias || edgePath != lock.path then
      throw (refusal ("source import path/alias differs: " ++ m.name))
    let some target := prior[lock.target]? | throw (refusal "imports must reference an earlier module")
    if edgePath != "./" ++ target.name ++ ".obend" then throw (refusal ("source import target differs: " ++ m.name))
    imports := imports ++ [⟨edgePath, edgeAlias, (edge.getObjVal? "span").toOption.getD .null, lock.target,
      target.name, target.sha256⟩]
  let module : SourceModule := ⟨m.name, source, Sha256.hex ⟨m.source.toArray⟩, imports⟩
  return (module, ← checkParsed module ast)

/-- The front end on the package's own sources. -/
def replay (p : ObjectiveSourcePackage.Package) : Except Diagnostic Lowering := do
  let mut modules : Array SourceModule := #[]
  let mut decoded : Array ObjectiveBendElaborate.Module := #[]
  for m in p.modules do
    let (module, d) ← replayModule modules m
    modules := modules.push module
    decoded := decoded.push d
  lowerDecoded modules.toList decoded.toList p.entryModule p.entryDefinition (Json.arr #[]) (Json.arr #[]) limits "definition"

/-- The canonical bytes of the typed-core packet the package publishes. -/
def publishedCore (p : ObjectiveSourcePackage.Package) : Except Diagnostic (List UInt8) := do
  let lowering ← replay p
  if let .error message := lowering.proposal then
    throw { stage := "objective-source-type-proposal", message }
  return lowering.packet.compress.toUTF8.toList

/-- `publishedCore` as an option: what the receiver compares an artifact's typed core with. -/
def replayedCore (p : ObjectiveSourcePackage.Package) : Option (List UInt8) := (publishedCore p).toOption

/-- What a replayed core IS: the rendering of the front end's lowering of the package's own
sources, whose typing proposal exists. -/
theorem replayedCore_is_lowering {p : ObjectiveSourcePackage.Package} {bytes : List UInt8}
    (replayed : replayedCore p = some bytes) :
    ∃ l, replay p = .ok l ∧ l.proposal.toBool = true ∧ l.packet.compress.toUTF8.toList = bytes := by
  unfold replayedCore publishedCore at replayed
  cases hr : replay p with
  | error e => simp [hr, bind, Except.bind, Except.toOption] at replayed
  | ok l =>
    cases hp : l.proposal with
    | error m => simp [hr, hp, bind, Except.bind, Except.toOption, throw, throwThe, MonadExceptOf.throw] at replayed
    | ok j =>
      refine ⟨l, rfl, by simp [hp, Except.toBool], ?_⟩
      simpa [hr, hp, bind, Except.bind, Except.toOption, pure, Except.pure] using replayed

end Minidregg.Compiler.ObjectiveBendPublication
