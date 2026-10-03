import Compiler.BendProofProjection
import Compiler.BendTraceSound
import Compiler.BendUnrolledIR2
import Compiler.ObliviousUnrollChecks
import Assurance.BendUnrolledSource

/- Focused reproducible target, using one qualified dependency closure.

General claims checked here:
* finite byte embedding and closed disclosure projection are canonical;
* arbitrary accepted field witnesses force the actual shared DAG;
* the generated fixed-tick DAG carries raw state and forces every successful
  network step, rather than assuming cross-row transition constraints.

The three finite examples are explicitly compiled checks. Native PCS soundness,
conditioned Fiat–Shamir analysis, full transcript hiding, constrained cSHAKE
commitments, native disclosure authority, source-loader denotation, full source
coverage and controller decode-step refinement are NOT consequences of this
module. No world proof admission is enabled by importing it. -/
namespace Minidregg.Assurance.BendArithmeticQualification
#assert_axioms Minidregg.Compiler.BendProofProjection.publicFields_injective
#assert_axioms Minidregg.Compiler.BendTraceSound.ir2_evaluates
#assert_axioms Minidregg.Compiler.ObliviousUnroll.build_success
#assert_axioms Minidregg.Compiler.BendUnrolledIR2.accepted_run
#assert_axioms Minidregg.Assurance.BendUnrolledSource.acceptedRun_source
#assert_compiled Minidregg.Compiler.ObliviousUnrollChecks.three_ticks
#assert_compiled Minidregg.Compiler.ObliviousUnrollChecks.refused_prefix
#assert_compiled Minidregg.Compiler.ObliviousUnrollChecks.zero_ticks
end Minidregg.Assurance.BendArithmeticQualification
