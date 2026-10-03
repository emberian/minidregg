/- Closed native output ABI for a persistent affine yield. The full source
result remains Tup Q1 planBytes capturedContinuation. Only the first component
is lowered to a Plan; no fabricated source trace to that component is used.
This decoder neither admits native effects nor consumes the continuation.
-/
import Compiler.BendPlanLowering

namespace Minidregg.Compiler.BendActivityPlanAdapter
open Minidregg.Theory.BendTT
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.Tower256ConcreteBackend
set_option autoImplicit false

def activityCodec : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.OUTPUT-CODEC/v1".toUTF8.toList
    "affine-Tup-Q1;canonical-complete-typed-Plan-first;retained-source-continuation-second/v1".toUTF8.toList).digest

structure Decoded (result : Term) where
  private mk ::
  planSource : Term
  continuation : Term
  plan : BendWorldPlan.Plan
  exactResult : result = .Tup .Q1 planSource continuation
  decodedPlan : BendPlanLowering.lower planSource = some plan

/-- The sole accepted shape for this registry branch. Failure does not try a
whole-Plan/scalar/other decoder or erase an ill-shaped continuation. -/
def lower (result : Term) : Option (Decoded result) :=
  match shape : result with
  | .Tup .Q1 planSource continuation =>
      match decoded : BendPlanLowering.lower planSource with
      | none => none
      | some plan => some ⟨planSource,continuation,plan,shape,decoded⟩
  | _ => none

theorem full_result {result : Term} (decoded : Decoded result) :
    result = .Tup .Q1 decoded.planSource decoded.continuation := decoded.exactResult

theorem plan_exact {result : Term} (decoded : Decoded result) :
    BendPlanLowering.lower decoded.planSource = some decoded.plan := decoded.decodedPlan

/-- A value proof about the complete actual source result entails that the
retained continuation is a source value. It does not establish its input type. -/
theorem continuation_value {book : Book} {result : Term} (decoded : Decoded result)
    (value : Value book result) : Value book decoded.continuation := by
  rw [decoded.exactResult] at value
  cases value with
  | tup _ second => exact second

#assert_axioms lower
#assert_axioms full_result
#assert_axioms plan_exact
#assert_axioms continuation_value
end Minidregg.Compiler.BendActivityPlanAdapter
