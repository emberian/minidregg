/- What an admitted Objective invocation's output IS, in source terms. Every
`ObjectiveBendNativeAdmission.Admitted` token carries the receiver's own
`executeWith` evidence on the checked applied source; by W1.4's
`execution_source_semantics` that run is a finished reference `runBounded` run of
the same term and the extracted Data (from which the plan and the result atom
are decoded) is A deep source evaluation of it. Caveat kept in every label:
`DeepEvaluates` is not yet proved deterministic, so this is "a deep evaluation",
not "the unique one". Lives in the ObjectiveProofs gate. -/
import Kernel.ObjectiveBendNativeAdmission
import Theory.ObjectiveBendDemandDataSoundness
import Theory.ObjectiveBendDemandTyping
namespace Minidregg.Kernel.ObjectiveBendAdmissionSemantics
open Minidregg.Compiler
open Minidregg.Kernel.ObjectiveBendNativeAdmission
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandDataSoundness
set_option autoImplicit false

theorem admitted_source_semantics {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable} {command : Command}
    {prepared : PreparedInvocation deployment profile ambient durable command}
    {ingress : List UInt8} {writes : List DataWrite} {guards : List ReadGuard}
    (admitted : Admitted prepared ingress writes guards) :
    runBounded (limits admitted.claim.capacity) (budget admitted.claim.capacity).ticks
        (initial admitted.core.applied.term) =
      .finished admitted.output.execution.value admitted.output.execution.state ∧
    DeepEvaluates admitted.core.applied.term admitted.output.execution.extraction.result.value :=
  execution_source_semantics
    (Minidregg.Theory.ObjectiveBendDemandTyping.source_scoped admitted.core.typed.derivation)
    admitted.output.execution

#assert_axioms admitted_source_semantics
end Minidregg.Kernel.ObjectiveBendAdmissionSemantics
