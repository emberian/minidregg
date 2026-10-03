/- Reverse structural representation laws for the admitted scalar output ABI.
Successful decoding fixes the complete constructor AST, not merely field values
or matching names. The base adapter retains current native receiving evidence. -/
import Compiler.BendScalarPlanAdapter
import Compiler.BendSourceCanonicalCodec

namespace Minidregg.Compiler.BendScalarPlanAdapter
open Minidregg.Compiler.BendSourceRepresentation
set_option autoImplicit false

theorem rootCodec_canonical {bytes : List UInt8} {root : Minidregg.Theory.TypedAuthorization.Digest}
    (decoded : rootCodec.decode bytes = some root) : rootCodec.encode root = bytes :=
  ResourceBirthCodec.strictCodec_canonical _ decoded

theorem decodeRef_sound (term : BTerm) (ref : Ref)
    (decoded : decodeRef term = some ref) : term = refTerm ref := by
  fun_cases decodeRef term <;>
    simp_all [decodeRef, refTerm, Option.bind_eq_some_iff] <;>
    aesop (add safe forward decodeNat_sound decodeBytes_sound)
      (add safe forward rootCodec_canonical)

theorem decodeWrite_sound (term : BTerm) (write : Write)
    (decoded : decodeWrite term = some write) : term = writeTerm write := by
  fun_cases decodeWrite term <;>
    simp_all [decodeWrite, writeTerm, Option.bind_eq_some_iff] <;>
    aesop (add safe forward decodeNat_sound)

theorem decodeList_sound {α : Type} (encoder : α → BTerm) (decoder : BTerm → Option α)
    (sound : ∀ term value, decoder term = some value → term = encoder value)
    (term : BTerm) (values : List α) (decoded : decodeList decoder term = some values) :
    term = listTerm encoder values := by
  fun_induction decodeList decoder term generalizing values <;>
    simp_all [decodeList, listTerm, Option.bind_eq_some_iff] <;> aesop

theorem decodeScalar_sound (term : BTerm) (scalar : Scalar)
    (decoded : decodeScalar term = some scalar) : term = scalarTerm scalar := by
  fun_cases decodeScalar term <;>
    simp_all [decodeScalar, scalarTerm, Option.bind_eq_some_iff] <;>
    aesop (add safe forward decodeRef_sound)
      (add safe forward (decodeList_sound writeTerm decodeWrite decodeWrite_sound))

theorem decodePlan_sound (term : BTerm) (plan : NativePlan)
    (decoded : decodePlan term = some plan) : term = planTerm plan := by
  fun_cases decodePlan term <;>
    simp_all [decodePlan, planTerm, Option.bind_eq_some_iff] <;>
    aesop
      (add safe forward (decodeList_sound refTerm decodeRef decodeRef_sound))
      (add safe forward (decodeList_sound scalarTerm decodeScalar decodeScalar_sound))

theorem decodeResult_sound (term : BTerm) (result : PlanResult)
    (decoded : decodeResult term = some result) : term = resultTerm result := by
  fun_cases decodeResult term <;>
    simp_all [decodeResult, resultTerm, Option.map_eq_some_iff] <;>
    aesop (add safe forward decodeNat_sound decodePlan_sound)

theorem decodeResult_iff (term : BTerm) (result : PlanResult) :
    decodeResult term = some result ↔ term = resultTerm result :=
  ⟨decodeResult_sound term result, fun equal => equal ▸ decode_resultTerm result⟩

#assert_axioms rootCodec_canonical
#assert_axioms decodeRef_sound
#assert_axioms decodeWrite_sound
#assert_axioms decodeList_sound
#assert_axioms decodeScalar_sound
#assert_axioms decodePlan_sound
#assert_axioms decodeResult_sound
#assert_axioms decodeResult_iff
end Minidregg.Compiler.BendScalarPlanAdapter
