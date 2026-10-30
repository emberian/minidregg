/-
# TokenCensus.NativePinSelfTest -- a planted `native_decide` under a standard-three pin must fail

Since Lean v4.35 `native_decide` rests on no core axiom (`Lean.ofReduceBool` and
`Lean.trustCompiler` are gone): each use is a generated `<theorem>._native.native_decide.ax_…`
axiom. `#assert_axioms` must still name it and refuse the theorem. Built by `CensusChecks`, never
imported by a census, so the planted axiom stays out of every tree count.
-/
import Theory.AssertAxioms

namespace Minidregg.TokenCensus.NativePinPlant

theorem plantedNative : (2 : Nat) ^ 10 = 1024 := by native_decide

theorem kernelChecked : (2 : Nat) ^ 10 = 1024 := by decide

#assert_axioms kernelChecked

/--
error: Minidregg.TokenCensus.NativePinPlant.plantedNative depends on axioms outside the standard three: [Minidregg.TokenCensus.NativePinPlant.plantedNative._native.native_decide.ax_1_1]
-/
#guard_msgs in #assert_axioms plantedNative

end Minidregg.TokenCensus.NativePinPlant
