import Assurance.BendObliviousFixtures
import Theory.AssertCompiled

namespace Minidregg.Assurance.BendObliviousControllerChecks
open Minidregg.Assurance.BendObliviousFixtures
theorem all_control_case_conformance : allConform = true := by native_decide
#assert_compiled all_control_case_conformance

theorem source_count_does_not_wrap : sourceCounterRefused = true := by native_decide
#assert_compiled source_count_does_not_wrap

end Minidregg.Assurance.BendObliviousControllerChecks
