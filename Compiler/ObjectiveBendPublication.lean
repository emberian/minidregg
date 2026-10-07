/- The typed core a source package publishes is a FUNCTION of the package.

`replay` runs the Lean front end (`ObjectiveBendFrontEnd`) on the package's own
source bytes: decode and fingerprint every module, parse it, lock each of its
parsed import edges to the module the package says it targets, lower the selected
declaration in definition mode with the publication type fuel. `publishedCore`
is the canonical bytes of the resulting typed-core packet.

The publisher signs exactly these bytes (`Host.ObjectivePackageAuthor.publication`).
A receiver holds a `Replayed` token (`replayAccept`): it re-ran the front end on the
package, the checker accepted the lowering (`ObjectiveBendFrontEnd.accept`), and the
artifact's typed core is byte-for-byte the rendering of that lowering. The receiver then
types and runs `accepted.source`, the elaborator's own term; the typed-core bytes are a
commitment it compared, never a value it parses. Native admission
(`ObjectiveBendNativeAdmission.SourceSelection`) and the activity kernel
(`ObjectiveActivity.publish`, `loadProgram`) both hold this token, and both require the
package to name this front end, so the package's `frontEnd` pin is not a label the
publisher asserts: it names the computation the receiver performs. -/
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

/-- The package's modules, decoded, parsed and locked (`replayModule`, in order): the part of the
front end that does not depend on which declaration is selected. A receiver that lowers two
declarations of one package (a call method beside the pinned entry, `ObjectiveCall.loadMethod`;
a migration, `ObjectiveActivity.loadMigration`) parses the sources ONCE. -/
def parsePackage (modules : List ObjectiveSourcePackage.Module) :
    Except Diagnostic (List SourceModule × List ObjectiveBendElaborate.Module) := do
  let mut parsed : Array SourceModule := #[]
  let mut decoded : Array ObjectiveBendElaborate.Module := #[]
  for m in modules do
    let (module, d) ← replayModule parsed m
    parsed := parsed.push module
    decoded := decoded.push d
  return (parsed.toList, decoded.toList)

/-- Lower one declaration of parsed modules in definition mode with the publication limits. -/
def lowerParsed (parsed : List SourceModule × List ObjectiveBendElaborate.Module) (entryModule : Nat)
    (entryDefinition : String) : Except Diagnostic Lowering :=
  lowerDecoded parsed.1 parsed.2 entryModule entryDefinition (Json.arr #[]) (Json.arr #[]) limits "definition"

/-- The front end on the package's own sources: parse every module, lower the selected declaration. -/
def replay (p : ObjectiveSourcePackage.Package) : Except Diagnostic Lowering := do
  let parsed ← parsePackage p.modules
  lowerParsed parsed p.entryModule p.entryDefinition

/-- **Another declaration of a parsed package is its replay**: lowering `definition` from the
package's parse is exactly the front end's replay of the package with `definition` selected. -/
theorem replay_select {p : ObjectiveSourcePackage.Package} {parsed : List SourceModule × List ObjectiveBendElaborate.Module}
    (parseExact : parsePackage p.modules = .ok parsed) (definition : String) :
    replay { p with entryDefinition := definition } = lowerParsed parsed p.entryModule definition := by
  simp only [replay, parseExact, bind, Except.bind]

/-- The canonical bytes of the typed-core packet the package publishes. -/
def publishedCore (p : ObjectiveSourcePackage.Package) : Except Diagnostic (List UInt8) := do
  let lowering ← replay p
  if let .error message := lowering.proposal then
    throw { stage := "objective-source-type-proposal", message }
  return lowering.packet.compress.toUTF8.toList

/-- The enforced laws the package publishes: the entry module's `law` declarations, as the
front end's replay of the package's own sources reads them. -/
def publishedLaws (p : ObjectiveSourcePackage.Package) : Except Diagnostic (List (String × ObjectiveBendLaw.LawExpr)) := do
  return (← replay p).laws

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

/-- A receiver's replay of a package against an offered typed core: the front end's lowering
of the package's sources, the checker's acceptance of it, the offered core is exactly its
rendering, and the checker fuel the rendering carries is within the receiver's capacity. -/
structure Replayed (p : ObjectiveSourcePackage.Package) (typedCore : List UInt8)
    (laws : List (String × ObjectiveBendLaw.LawExpr)) (maxFuel : Nat) where
  private mk ::
  /-- The package's parse, which another declaration of it is lowered from (`replay_select`). -/
  parsed : List SourceModule × List ObjectiveBendElaborate.Module
  parseExact : parsePackage p.modules = .ok parsed
  lowering : Lowering
  lowerExact : lowerParsed parsed p.entryModule p.entryDefinition = .ok lowering
  accepted : Accepted lowering
  coreExact : lowering.packet.compress.toUTF8.toList = typedCore
  /-- The offered laws are exactly the laws the front end reads from the package's source. -/
  lawsExact : lowering.laws = laws
  fuelWithin : accepted.packet.fuel ≤ maxFuel

/-- A replay token's lowering is the front end's replay of the package. -/
theorem Replayed.replayExact {p : ObjectiveSourcePackage.Package} {typedCore : List UInt8}
    {laws : List (String × ObjectiveBendLaw.LawExpr)} {maxFuel : Nat}
    (r : Replayed p typedCore laws maxFuel) : replay p = .ok r.lowering := by
  simp only [replay, r.parseExact, bind, Except.bind]
  exact r.lowerExact

def replayAccept (p : ObjectiveSourcePackage.Package) (typedCore : List UInt8)
    (laws : List (String × ObjectiveBendLaw.LawExpr)) (maxFuel : Nat) :
    Except Diagnostic (Replayed p typedCore laws maxFuel) :=
  match parseExact : parsePackage p.modules with
  | .error d => throw d
  | .ok parsed =>
  match lowerExact : lowerParsed parsed p.entryModule p.entryDefinition with
  | .error d => throw d
  | .ok lowering => do
    let accepted ← accept lowering
    if core : lowering.packet.compress.toUTF8.toList = typedCore then
      if lawsSame : lowering.laws = laws then
        if fuel : accepted.packet.fuel ≤ maxFuel then pure ⟨parsed, parseExact, lowering, lowerExact, accepted, core, lawsSame, fuel⟩
        else throw (refusal "typed core checker fuel exceeds the receiver's capacity")
      else throw (refusal "offered laws differ from the front end's replay of the package")
    else throw (refusal "offered typed core differs from the front end's replay of the package")

/-- **A replay token's laws are the package's**: the ones `publishedLaws` reads from its source. -/
theorem Replayed.laws_replayed {p : ObjectiveSourcePackage.Package} {typedCore : List UInt8}
    {laws : List (String × ObjectiveBendLaw.LawExpr)} {maxFuel : Nat}
    (r : Replayed p typedCore laws maxFuel) : publishedLaws p = .ok laws := by
  have lawsSame := r.lawsExact
  unfold publishedLaws
  rw [r.replayExact]
  simp [bind, Except.bind, pure, Except.pure, lawsSame]

/-- A replay token's core is the one `replayedCore` computes. -/
theorem Replayed.core_replayed {p : ObjectiveSourcePackage.Package} {typedCore : List UInt8}
    {laws : List (String × ObjectiveBendLaw.LawExpr)} {maxFuel : Nat}
    (r : Replayed p typedCore laws maxFuel) : ObjectiveBendPublication.replayedCore p = some typedCore := by
  unfold replayedCore publishedCore
  have core := r.coreExact
  simp only [String.toUTF8] at core
  simp [r.replayExact, r.accepted.proposed, bind, Except.bind, Except.toOption, pure, Except.pure, core]

#assert_axioms replayedCore_is_lowering
#assert_axioms replay_select
#assert_axioms Replayed.replayExact
#assert_axioms Replayed.core_replayed
#assert_axioms Replayed.laws_replayed
end Minidregg.Compiler.ObjectiveBendPublication
