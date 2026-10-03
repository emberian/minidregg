/- General facts about the actual physical codec, not a second encoding.
The word theorem is the common base for arbitrary-width field decoding.
Whole-state decode/encode and all-reachable raw-wire conformance remain open. -/
import Compiler.BendObliviousCodec

namespace Minidregg.Compiler.BendObliviousCodecRefinement
open Minidregg.Theory
open BendObliviousCodec
set_option autoImplicit false

theorem natBits_length (width value : Nat) :
    (BendClosurePacking.natBits width value).length = width := by
  simp [BendClosurePacking.natBits]

theorem natBits_read_modulo (width value : Nat) :
    (BitVec.ofBoolListLE (BendClosurePacking.natBits width value)).toNat =
      value % 2^width := by
  apply Nat.eq_of_testBit_eq
  intro bit
  change (BitVec.ofBoolListLE (BendClosurePacking.natBits width value)).getLsbD bit = _
  rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    Nat.testBit_mod_two_pow]
  by_cases inside : bit < width
  · simp [BendClosurePacking.natBits, List.getElem?_range inside, inside]
  · have beyond : (List.range width)[bit]? = none :=
      List.getElem?_eq_none (by simp; omega)
    simp [BendClosurePacking.natBits, beyond, inside]

/-- The same strict range checked by physical encode prevents truncation. -/
theorem natBits_read_exact {width value : Nat} (fits : value < 2^width) :
    (BitVec.ofBoolListLE (BendClosurePacking.natBits width value)).toNat = value := by
  rw [natBits_read_modulo, Nat.mod_eq_of_lt fits]

#assert_axioms natBits_length
#assert_axioms natBits_read_modulo
#assert_axioms natBits_read_exact
end Minidregg.Compiler.BendObliviousCodecRefinement
