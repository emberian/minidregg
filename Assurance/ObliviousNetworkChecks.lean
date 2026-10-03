/- Executed circuit conformance checks, explicitly compiler-trusting.
General gate/address laws remain separately kernel-audited in ObliviousGate. -/
import Compiler.ObliviousNetwork
import Theory.AssertCompiled

namespace Minidregg.Assurance.ObliviousNetworkChecks
open Minidregg.Compiler.ObliviousGate
open Minidregg.Compiler.ObliviousNetwork
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

def shape : HeapShape := ⟨3, 8, 2, by decide⟩
def bits (width value : Nat) : Array Bool := (List.range width).toArray.map value.testBit
/-- Eight-bit rows represent fixed shape payloads, including their tags. -/
def rows : Array Bool := bits 8 19 ++ bits 8 74 ++ bits 8 173

theorem read_dag_valid : (readNetwork shape).valid = true := by native_decide

theorem write_dag_valid : (writeNetwork shape).valid = true := by native_decide

theorem selected_row_exact :
    (readNetwork shape).evaluate (bits 2 2 ++ rows) = some (#[true] ++ bits 8 173) := by native_decide

theorem invalid_address_distinct_from_zero :
    (readNetwork shape).evaluate (bits 2 3 ++ rows) = some (#[false] ++ bits 8 0) := by native_decide

theorem write_one_row_exact :
    (writeNetwork shape).evaluate (bits 2 1 ++ rows ++ bits 8 255) =
      some (#[true] ++ bits 8 19 ++ bits 8 255 ++ bits 8 173) := by native_decide

theorem invalid_write_preserves_rows :
    (writeNetwork shape).evaluate (bits 2 3 ++ rows ++ bits 8 255) =
      some (#[false] ++ rows) := by native_decide

theorem input_shape_refuses :
    (readNetwork shape).evaluate (bits 2 2) = none := by native_decide

theorem increment_dag_exact :
    (incrementNetwork 8).evaluate (bits 8 127) = some (#[false] ++ bits 8 128) := by native_decide

theorem increment_dag_overflow :
    (incrementNetwork 8).evaluate (bits 8 255) = some (#[true] ++ bits 8 0) := by native_decide

theorem read_multiplicative_depth :
    (readNetwork shape).census.andDepth = 3 := by native_decide

theorem read_and_census :
    (readNetwork shape).census.ands = 30 := by native_decide

#assert_compiled read_multiplicative_depth
#assert_compiled read_and_census
#assert_compiled read_dag_valid
#assert_compiled write_dag_valid
#assert_compiled selected_row_exact
#assert_compiled invalid_address_distinct_from_zero
#assert_compiled write_one_row_exact
#assert_compiled invalid_write_preserves_rows
#assert_compiled input_shape_refuses
#assert_compiled increment_dag_exact
#assert_compiled increment_dag_overflow

end Minidregg.Assurance.ObliviousNetworkChecks
