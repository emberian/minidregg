/- Consume the actual checked code-sharing compiler through the SAME source
certificate and fixed-controller producer. No new evaluator or source semantics.
The lowered representation edition is separate from source identity. -/
import Compiler.BendObliviousExecution
import Compiler.BendClosureCompileIndexed

namespace Minidregg.Compiler.BendObliviousExecutionIndexed
open Minidregg.Theory BendTT
set_option autoImplicit false

def prepare (book : Book) (publicTemplate : Term) (shape : BendObliviousState.Shape) :
    Option (BendObliviousExecution.Prepared book publicTemplate shape) := do
  let compiled ← BendClosureCompileIndexed.compile book publicTemplate
  BendObliviousExecution.ofCompiled shape compiled

end Minidregg.Compiler.BendObliviousExecutionIndexed
