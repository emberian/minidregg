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
import Theory.ObjectiveBendDemandPreservation
import Compiler.ObjectiveBendFrontEndAdequacy
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

/-- An admitted invocation runs the front end's own output on its package, and it cannot
refuse. The package names THIS receiver's front end (`ObjectiveBendFrontEndIdentity.identity`,
by way of the policy's pin); the receiver re-ran that front end on the package's sources
(`replay`), the checker accepted the lowering, and the artifact's typed core is byte-for-byte
the lowering's rendering, whose decoded term IS the elaborator's erased term (a theorem,
`ObjectiveBendTermWire.decode_json`, not a comparison). The term the receiver checked and ran
is that erased term applied to the authenticated input. Neither the definition alone
(`accepted_never_refused`) nor the applied term the invocation ran ever reaches a refusal of
the bounded demand machine, at any tick, heap or stack budget. No publisher-supplied core is
admitted on the strength of a label, and no core bytes are parsed on the way. -/
theorem admitted_front_end {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable} {command : Command}
    {prepared : PreparedInvocation deployment profile ambient durable command}
    {ingress : List UInt8} {writes : List DataWrite} {guards : List ReadGuard}
    (admitted : Admitted prepared ingress writes guards) :
    admitted.core.source.package.package.frontEnd = ObjectiveBendFrontEndIdentity.identity ∧
    ∃ (l : ObjectiveBendFrontEnd.Lowering) (a : ObjectiveBendFrontEnd.Accepted l),
      ObjectiveBendPublication.replay admitted.core.source.package.package = .ok l ∧
      l.packet.compress.toUTF8.toList = admitted.core.source.loaded.artifact.typedCore ∧
      a.packet.source.term = a.erased ∧
      admitted.core.applied.term = .app a.erased admitted.core.inputTerm ∧
      (∀ (limits : Limits) (ticks : Nat) (reason : Minidregg.Theory.ObjectiveBendDemandMachine.Refusal)
          (retained : Minidregg.Theory.ObjectiveBendDemandMachine.State),
        runBounded limits ticks (initial a.erased) ≠ .refused reason retained) ∧
      (∀ (limits : Limits) (ticks : Nat) (reason : Minidregg.Theory.ObjectiveBendDemandMachine.Refusal)
          (retained : Minidregg.Theory.ObjectiveBendDemandMachine.State),
        runBounded limits ticks (initial admitted.core.applied.term) ≠ .refused reason retained) := by
  let r := admitted.core.source.replayed
  refine ⟨admitted.core.source.frontEndExact.trans admitted.core.source.frontEndOwn,
    r.lowering, r.accepted, r.replayExact, r.coreExact, r.accepted.packetTerm, ?_,
    ObjectiveBendFrontEndAdequacy.accepted_never_refused r.lowering r.accepted, ?_⟩
  · show (ObjectiveBendNativeInput.instantiate r.accepted.source admitted.core.inputTerm).term = _
    simp only [ObjectiveBendNativeInput.instantiate, r.accepted.sourceExact]
  · intro limits ticks reason retained
    exact Minidregg.Theory.ObjectiveBendDemandPreservation.typed_runBounded_no_refusal
      (Minidregg.Theory.ObjectiveBendDemandTyping.checked_initial_state _ admitted.core.typed)
      limits ticks reason retained

#assert_axioms admitted_front_end
end Minidregg.Kernel.ObjectiveBendAdmissionSemantics
