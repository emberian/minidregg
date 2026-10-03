import Compiler.ObliviousUnrollSemantics
import Theory.AssertCompiled
namespace Minidregg.Compiler.ObliviousUnrollChecks
open ObliviousNetwork ObliviousUnroll

def flip : Network :=
  { inputCount := 1, gates := #[.constant true, .xor 0 1], outputs := #[1, 2] }
def hostile : Network :=
  { inputCount := 1, gates := #[.constant true, .xor 0 1], outputs := #[0, 2] }

/-- Three real state-dependent copies carry each previous output into the next. -/
theorem three_ticks : (build flip 3).network.evaluate #[false] = some #[true, true] := by native_decide
/-- A later successful handled bit cannot erase an earlier refusal. -/
theorem refused_prefix : (build hostile 2).network.evaluate #[false] = some #[false, false] := by native_decide
/-- Zero capacity preserves input and emits the explicitly counted true gate. -/
theorem zero_ticks : (build flip 0).network.evaluate #[true] = some #[true, true] := by native_decide
#assert_compiled three_ticks
#assert_compiled refused_prefix
#assert_compiled zero_ticks
end Minidregg.Compiler.ObliviousUnrollChecks
