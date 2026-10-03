/- Reverse source representation theorem, separate from the executable Plan
ABI so forward decoding/execution consumers do not await stronger codec proof. -/
import Compiler.BendPlanLowering
import Compiler.BendSourceCanonicalCodec
namespace Minidregg.Compiler.BendPlanLowering
open Minidregg.Theory
open Minidregg.Theory.BendTT
set_option autoImplicit false
/-- Successful lowering retains the entire exact source representation. It
cannot discard unknown payload fields, reorder actions or wrap oversized bytes. -/
theorem lower_sound {result : BendTT.Term} {plan : BendWorldPlan.Plan}
    (h : lower result = some plan) : result = sourceTerm plan := by
  unfold lower at h
  cases decoded : BendSourceRepresentation.decodeBytes result with
  | none => simp [decoded] at h
  | some bytes =>
      have native : decode bytes = some plan := by simpa [decoded] using h
      have source : result = BendSourceRepresentation.bytesTerm bytes :=
        (BendSourceRepresentation.decodeBytes_iff result bytes).mp decoded
      rw [source, ← canonical native]
      rfl


end Minidregg.Compiler.BendPlanLowering
