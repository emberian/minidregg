/- Shared fixed-access Bend controller assembly (construction in progress).
Every block reads the SAME input state; chaining block outputs would incorrectly
execute multiple microsteps when one block changes to another block's tag.
The explicit handled output is false until the corresponding actual control is
implemented. Consumers must refuse unhandled; it is never successful execution.
Current coverage: lookup1/2, unspine5, complete8, refused9, reverse10, install11.
-/ 
import Compiler.BendObliviousLookup
import Compiler.BendObliviousUnspine

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
    let afterLookup ← muxState lookupHandled lookup admin
    let afterUnspine ← muxState unspineHandled unspine afterLookup
    let handled ← emit (.xor adminHandled lookupHandled)
    let handled ← emit (.xor handled unspineHandled)
    modify fun graph => {graph with outputs := #[handled] ++ afterUnspine.outputs}
  pure (work.run {inputCount := size}).2

/-- Public-only construction guard. An actual validated closure compiler result
and source admission are still required by the caller; this is not authority.
The whole shape/code/name table is public in this profile. -/
def network (shape : Shape) (library : BendClosureMachine.Library) : Option Network :=
  if !shape.valid then none
  else if fits : shape.heapSlots ≤ 2^shape.wordBits then
    let limits : BendClosureMachine.Limits :=
      ⟨⟨shape.heapSlots,shape.wordBits,fits⟩,shape.frameSlots,shape.argumentSlots⟩
    if !library.fits limits then none
    else if library.program.names.toList.Nodup then some (build shape library)
    else none
  else none

end Minidregg.Compiler.BendObliviousController
