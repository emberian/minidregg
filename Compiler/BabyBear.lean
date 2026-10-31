/-
The shared executable prime field. These declarations are moved unchanged
from EmitSerialize so a native receiver need not import descriptor-emission
examples and their unrelated compiler closure just to select its field.
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum.Prime

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Compiler

/-- BabyBear `p = 2^31 - 2^27 + 1`. -/
def babyBearP : ℕ := 2013265921

theorem babyBearP_eq : babyBearP = 2 ^ 31 - 2 ^ 27 + 1 := by decide

instance : NeZero babyBearP := ⟨by norm_num [babyBearP]⟩

-- norm_num's primality certificate for a 31-bit prime nests past the default kernel depth.
set_option maxRecDepth 8192 in
instance : Fact (Nat.Prime babyBearP) := ⟨by norm_num [babyBearP]⟩

abbrev BabyBear := ZMod babyBearP

end Minidregg.Compiler
