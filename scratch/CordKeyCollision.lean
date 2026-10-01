/- E3 input (not in any umbrella): a free-key Sample record does not encode injectively under Nock cords. -/
import Kernel.NockProgramCell
open Minidregg.Kernel.NockProgramCell
theorem cord_key_collision : cord "a" = cord "a\u0000" := by decide +kernel
theorem cord_keys_distinct : "a" ≠ "a\u0000" := by decide
