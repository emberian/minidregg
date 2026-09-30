/-
# `#assert_axioms` — a named theorem's axiom footprint, as a check that can fail

`#assert_axioms foo` elaborates to nothing when `foo` depends on no axiom
outside Lean's three standard ones (`propext`, `Classical.choice`,
`Quot.sound`), and is an error otherwise.  `sorryAx` and `Lean.ofReduceBool`
(the compiler trust of `native_decide`) are therefore refused.
-/
import Lean

namespace Minidregg.Kernel.AssertAxioms

open Lean Elab Command

/-- The axioms a kernel-checked Mini theorem may rest on. -/
def standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]

elab "#assert_axioms " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axioms ← liftCoreM <| collectAxioms name
  let outside := axioms.toList.filter (fun axiomName => !standard.contains axiomName)
  unless outside.isEmpty do
    throwError m!"{name} depends on axioms outside the standard three: {outside}"

end Minidregg.Kernel.AssertAxioms
