import Compiler.BabyBear
import Theory.AssertAxioms

/- Exact canonical-byte embedding shared by proof input and private commitment
relations. This module does not choose which bytes may be disclosed. In
particular, BendInvocation.Result contains private release bytes and cannot be
published wholesale by default. -/
namespace Minidregg.Compiler.BendProofBytes
set_option autoImplicit false

def fieldByte (byte : UInt8) : BabyBear := (byte.toNat : BabyBear)
def fields (bytes : List UInt8) : List BabyBear := bytes.map fieldByte

theorem fieldByte_val (byte : UInt8) : (fieldByte byte).val = byte.toNat := by
  apply ZMod.val_natCast_of_lt
  have bound := byte.toNat_lt_size
  change byte.toNat < 2013265921
  omega

theorem fieldByte_injective : Function.Injective fieldByte := by
  intro left right same
  apply UInt8.toNat.inj
  have h := congrArg ZMod.val same
  simpa only [fieldByte_val] using h

/-- Equality of complete vectors includes length. No padded scalar fold or
modularly reduced 32-bit limb is used to stand for a digest. -/
theorem fields_injective : Function.Injective fields := by
  intro left right same
  exact fieldByte_injective.list_map same

theorem fields_length (bytes : List UInt8) : (fields bytes).length = bytes.length := by
  simp [fields]

#assert_axioms fieldByte_val
#assert_axioms fieldByte_injective
#assert_axioms fields_injective
#assert_axioms fields_length
end Minidregg.Compiler.BendProofBytes
