/- Signed literal serialization before finite-field reduction. Consumers admit
only their declared denominator and coefficient domain; Rat→Fp has no global
ring homomorphism. This encoding preserves provenance, not encryption proofs. -/
import Compiler.EmitSerialize
import Mathlib.Algebra.Field.Rat

namespace Minidregg.Compiler.BendLogicSerialize

open Lean (Json toJson)

def signedWire : DWire Rat → Json
  | .cnst c => Json.mkObj [("z", toJson c.num), ("den", toJson c.den)]
  | .wire n => Json.mkObj [("w", toJson n)]

def signedGate (g : DGate Rat) : Json :=
  Json.mkObj [("op", gateOpToJson g.op), ("a", signedWire g.a),
    ("b", signedWire g.b), ("out", toJson g.out)]

end Minidregg.Compiler.BendLogicSerialize
