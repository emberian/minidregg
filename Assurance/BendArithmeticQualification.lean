import Assurance.ObjectiveBendCommittedSource
import Compiler.ObjectiveProofContext
import Compiler.BendTraceSound
import Compiler.BendUnrolledIR2
import Compiler.ObliviousUnrollChecks

/- Historical build-target name; sole active source meaning is Objective Bend.

General claims checked here:
* exact context/coins/payload serialization is injective (not the hash);
* arbitrary accepted arithmetic witnesses force the shared Boolean graph;
* fixed physical runs yield actual lazy Objective source observations/values
  WHEN the concrete controller supplies PackedRefinement and its output codec.

The generic unroll checks below exercise finite networks. They do not construct
that missing controller refinement, establish source completeness, prove native
PCS/Fiat-Shamir security or transcript hiding, or authorize a world effect.
No old BendTT evaluator or its termination theorem occurs in this target.
-/
namespace Minidregg.Assurance.BendArithmeticQualification
#assert_axioms Minidregg.Compiler.ObjectiveProofContext.preimage_injective
#assert_axioms Minidregg.Compiler.BendTraceSound.ir2_evaluates
#assert_axioms Minidregg.Compiler.ObliviousUnroll.build_success
#assert_axioms Minidregg.Compiler.BendUnrolledIR2.accepted_run
#assert_axioms Minidregg.Assurance.ObjectiveBendProofSource.accepted_trace
#assert_axioms Minidregg.Assurance.ObjectiveBendCommittedSource.arithmetic_observes_source
#assert_axioms Minidregg.Assurance.ObjectiveBendCommittedSource.arithmetic_returns_source_value
#assert_compiled Minidregg.Compiler.ObliviousUnrollChecks.three_ticks
#assert_compiled Minidregg.Compiler.ObliviousUnrollChecks.refused_prefix
#assert_compiled Minidregg.Compiler.ObliviousUnrollChecks.zero_ticks
end Minidregg.Assurance.BendArithmeticQualification
