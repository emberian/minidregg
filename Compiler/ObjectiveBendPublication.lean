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

/-- A receiver's replay of a package against an offered typed core: the front end's lowering
of the package's sources, the checker's acceptance of it, the offered core is exactly its
rendering, and the checker fuel the rendering carries is within the receiver's capacity. -/
structure Replayed (p : ObjectiveSourcePackage.Package) (typedCore : List UInt8) (maxFuel : Nat) where
  private mk ::
  lowering : Lowering
  replayExact : replay p = .ok lowering
  accepted : Accepted lowering
  coreExact : lowering.packet.compress.toUTF8.toList = typedCore
  fuelWithin : accepted.packet.fuel ≤ maxFuel

def replayAccept (p : ObjectiveSourcePackage.Package) (typedCore : List UInt8) (maxFuel : Nat) :
    Except Diagnostic (Replayed p typedCore maxFuel) :=
  match replayed : replay p with
  | .error d => throw d
  | .ok lowering => do
    let accepted ← accept lowering
    if core : lowering.packet.compress.toUTF8.toList = typedCore then
      if fuel : accepted.packet.fuel ≤ maxFuel then pure ⟨lowering, replayed, accepted, core, fuel⟩
      else throw (refusal "typed core checker fuel exceeds the receiver's capacity")
    else throw (refusal "offered typed core differs from the front end's replay of the package")

/-- A replay token's core is the one `replayedCore` computes. -/
theorem Replayed.core_replayed {p : ObjectiveSourcePackage.Package} {typedCore : List UInt8} {maxFuel : Nat}
    (r : Replayed p typedCore maxFuel) : ObjectiveBendPublication.replayedCore p = some typedCore := by
  unfold replayedCore publishedCore
  have core := r.coreExact
  simp only [String.toUTF8] at core
  simp [r.replayExact, r.accepted.proposed, bind, Except.bind, Except.toOption, pure, Except.pure, core]

#assert_axioms replayedCore_is_lowering
#assert_axioms Replayed.core_replayed
end Minidregg.Compiler.ObjectiveBendPublication
