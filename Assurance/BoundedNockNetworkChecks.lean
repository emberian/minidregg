import Assurance.BoundedNockRefinement

namespace Minidregg.Assurance.BoundedNockNetworkChecks
open Minidregg.Compiler.BoundedNockCircuit
open Minidregg.Compiler.BoundedNockNetwork
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

def shape : HeapShape := ⟨3, 2, 2, by decide⟩
def bits (width value : Nat) : Array Bool := (List.range width).toArray.map value.testBit
/-- Eight-bit rows represent fixed shape payloads, including their tags. -/
def rows : Array Bool := bits 8 19 ++ bits 8 74 ++ bits 8 173

theorem read_dag_valid : (readNetwork shape).valid = true := by decide +kernel

theorem write_dag_valid : (writeNetwork shape).valid = true := by decide +kernel

theorem selected_row_exact :
    (readNetwork shape).evaluate (bits 2 2 ++ rows) = some (#[true] ++ bits 8 173) := by decide +kernel

theorem invalid_address_distinct_from_zero :
    (readNetwork shape).evaluate (bits 2 3 ++ rows) = some (#[false] ++ bits 8 0) := by decide +kernel

theorem write_one_row_exact :
    (writeNetwork shape).evaluate (bits 2 1 ++ rows ++ bits 8 255) =
      some (#[true] ++ bits 8 19 ++ bits 8 255 ++ bits 8 173) := by decide +kernel

theorem invalid_write_preserves_rows :
    (writeNetwork shape).evaluate (bits 2 3 ++ rows ++ bits 8 255) =
      some (#[false] ++ rows) := by decide +kernel

theorem input_shape_refuses :
    (readNetwork shape).evaluate (bits 2 2) = none := by decide +kernel

theorem increment_dag_exact :
    (incrementNetwork 8).evaluate (bits 8 127) = some (#[false] ++ bits 8 128) := by decide +kernel

theorem increment_dag_overflow :
    (incrementNetwork 8).evaluate (bits 8 255) = some (#[true] ++ bits 8 0) := by decide +kernel

#assert_axioms read_dag_valid
#assert_axioms write_dag_valid
#assert_axioms selected_row_exact
#assert_axioms invalid_address_distinct_from_zero
#assert_axioms write_one_row_exact
#assert_axioms invalid_write_preserves_rows
#assert_axioms input_shape_refuses
#assert_axioms increment_dag_exact
#assert_axioms increment_dag_overflow

end Minidregg.Assurance.BoundedNockNetworkChecks
