/-
The shared executable prime field. These declarations are moved unchanged
from EmitSerialize so a native receiver need not import descriptor-emission
examples and their unrelated compiler closure just to select its field.
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

namespace Minidregg.Compiler

/-- BabyBear `p = 2^31 - 2^27 + 1`. -/
def babyBearP : ℕ := 2013265921

theorem babyBearP_eq : babyBearP = 2 ^ 31 - 2 ^ 27 + 1 := by decide

instance : NeZero babyBearP := ⟨by norm_num [babyBearP]⟩

instance : Fact (Nat.Prime babyBearP) := ⟨by norm_num [babyBearP]⟩

abbrev BabyBear := ZMod babyBearP

end Minidregg.Compiler
