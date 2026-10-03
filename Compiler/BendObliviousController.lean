/- Shared fixed-access Bend controller assembly (construction in progress).
Every block reads the SAME input state; chaining block outputs would incorrectly
execute multiple microsteps when one block changes to another block's tag.
The explicit handled output is false until the corresponding actual control is
implemented. Consumers must refuse unhandled; it is never successful execution.
All twelve source controls are now authored. Qualification remains pending.
Counter overflow clears handled and preserves input; no source success wraps.
-/ 
import Compiler.BendObliviousLookup
import Compiler.BendObliviousUnspine
import Compiler.BendObliviousWalk

namespace Minidregg.Compiler.BendObliviousController
open Minidregg.Theory
open ObliviousNetwork ObliviousWords BendObliviousState
open BendObliviousProgram
set_option autoImplicit false

def build (shape : Shape) (library : BendClosureMachine.Library) : Network := Id.run do
  let (state,size) := (stateInputs shape).run 0
  let work : Builder Unit := do
    let zero ← emit (.constant false)
    let one ← emit (.constant true)
    let rom ← BendObliviousProgram.build shape library
    let (adminHandled,admin) ← BendObliviousAdministrative.block zero one state
    let (lookupHandled,lookup) ← BendObliviousLookup.block zero one state
    let (unspineHandled,unspine) ← BendObliviousUnspine.block zero one rom state
    let (evaluateHandled,evaluated) ← BendObliviousEvaluate.block zero one rom state
    let (returnHandled,returned) ← BendObliviousReturn.block zero one rom state
    let (applyHandled,applied) ← BendObliviousApply.block zero one rom state
    let (walkHandled,walked) ← BendObliviousWalk.block zero one rom state
    let afterLookup ← muxState lookupHandled lookup admin
    let afterUnspine ← muxState unspineHandled unspine afterLookup
    let afterEvaluate ← muxState evaluateHandled evaluated afterUnspine
    let afterReturn ← muxState returnHandled returned afterEvaluate
    let afterApply ← muxState applyHandled applied afterReturn
    let afterWalk ← muxState walkHandled walked afterApply
    let handled ← emit (.xor adminHandled lookupHandled)
    let handled ← emit (.xor handled unspineHandled)
    let handled ← emit (.xor handled evaluateHandled)
    let handled ← emit (.xor handled returnHandled)
    let handled ← emit (.xor handled applyHandled)
    let handled ← emit (.xor handled walkHandled)
    modify fun graph => {graph with outputs := #[handled] ++ afterWalk.outputs}
  pure (work.run {inputCount := size}).2

/-- Public-only construction guard. An actual validated closure compiler result
and source admission are still required by the caller; this is not authority.
The whole shape/code/name table is public in this profile. -/
def network (shape : Shape) (library : BendClosureMachine.Library) : Option Network :=
  if !shape.valid || shape.argumentSlots = 0 then none
  else if fits : shape.heapSlots ≤ 2^shape.wordBits then
    let limits : BendClosureMachine.Limits :=
      ⟨⟨shape.heapSlots,shape.wordBits,fits⟩,shape.frameSlots,shape.argumentSlots⟩
    if !library.fits limits then none
    else if library.program.names.toList.Nodup then some (build shape library)
    else none
  else none

end Minidregg.Compiler.BendObliviousController
