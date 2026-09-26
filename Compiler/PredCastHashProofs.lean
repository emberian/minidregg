/-
The cast-alias obligation depends on which source integers occur, not their
order or repetition. This is the semantic law used by the compiled hashed
decision in PredCompile; it does not weaken collision refusal.
-/
import Compiler.PredCompile

namespace Minidregg.Compiler.PredCastHashProofs

variable {F : Type} [Field F]

theorem castInjOn_extensional (I J : List ℤ)
    (same : ∀ x, x ∈ I ↔ x ∈ J) :
    castInjOn F I ↔ castInjOn F J := by
  constructor
  · intro checked a ha b hb
    exact checked a ((same a).mpr ha) b ((same b).mpr hb)
  · intro checked a ha b hb
    exact checked a ((same a).mp ha) b ((same b).mp hb)

theorem duplicate_values_decision [DecidableEq F] (I : List ℤ) :
    decide (castInjOn F (I ++ I)) = decide (castInjOn F I) := by
  exact decide_eq_decide.mpr (castInjOn_extensional (I ++ I) I (by simp))

end Minidregg.Compiler.PredCastHashProofs
