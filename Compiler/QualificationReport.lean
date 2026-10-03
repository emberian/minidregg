import Theory.AssertAxioms
import Lean

/- Emit declarations from the elaborated environment. Axiom accounting constrains
trust; this command deliberately makes no adequacy or witness-existence claim. -/
namespace Minidregg.Compiler.QualificationReport
open Lean Elab Command
open Minidregg.Theory.AssertAxioms

elab "#emit_qualification_claims" : command => do
  let env ← getEnv
  for (name, info) in env.constants.map₁.toList do
    unless info matches .thmInfo _ do continue
    let some module := packageModule? env name | continue
    let statement ← liftTermElabM fun _ => Meta.ppExpr info.type
    let axioms ← liftCoreM <| collectAxioms name
    let outside := axioms.toList.filter (fun axiomName => !standard.contains axiomName)
    let trust := if outside.isEmpty then "kernel-standard"
      else if outside.all isCompilerTrust then "compiled"
      else "outside-standard"
    let row := Json.mkObj [("module", toJson module.toString),
      ("theorem", toJson name.toString), ("statement", toJson statement.pretty),
      ("axioms", toJson (axioms.toList.map Name.toString)), ("trust", toJson trust),
      ("witnesses", toJson "not inferred; require named checked witnesses")]
    logInfo m!"QUALIFICATION_CLAIM {row.compress}"
end Minidregg.Compiler.QualificationReport
