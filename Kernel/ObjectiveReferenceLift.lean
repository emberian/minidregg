/- The kernel's activity turns against the reference interaction tree (ObjectiveProofs).

`Theory.ObjectiveBendInteraction` gives an activity program its reference meaning: the
interaction tree of the program's OWN machine (`node`, `observe`, `continuation`), with no
checkpointing and resources only as large as needed. `Kernel.ObjectiveResumeContract` proves,
for one stored checkpoint, that the difference between resuming it and resuming the program's
own yield is resources only (`runSegment_stored_converse`, `runSegment_stored_next`). This
module lifts that through the kernel's handlers:

* `birth_reference`, `birth_reference_vis`: a birth commits the reference node of the
  program's initial state; when it yields, that node is `vis d` with `decodePlan d` the
  birth's Plan, and the checkpoint the birth stores is in a `Chain` with the program's own
  yielded state (the reference's continuation point);
* `delivery_reference`: a delivery whose decoded checkpoint is in a `Chain` with a reference
  yield `y` resumes, for the delivered response `r`, a state in a chain with `resume r y`;
  if its segment is the bounded run's own (`runSegment`, not a program fault the handler made
  of a refusal), that segment is the reference node at `resume r y`, and if it yielded the
  checkpoint it stores is in a `Chain` with the reference's own next yield;
  `Delivery.ran_or_fault` says what the other case is;
* `exhaustion_reference`: an exhaustion resumes the same way, commits no ending, and leaves
  the checkpoint (so the chain) as it was. -/
import Kernel.ObjectiveResumeContract
import Kernel.ObjectiveCheckpointInvariant

namespace Minidregg.Kernel.ObjectiveReferenceLift
open Minidregg.Theory Minidregg.Compiler
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ObjectiveActivityWire
open Minidregg.Kernel.ObjectiveActivity
open Minidregg.Kernel.ObjectiveResumeContract
open Minidregg.Theory.ObjectiveBendTyping
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandTyping
open Minidregg.Theory.ObjectiveBendDemandPreservation
open Minidregg.Theory.ObjectiveBendDemandForcing (Chain Ending endsWith EndsAbove)
open Minidregg.Theory.ObjectiveBendInteraction (Node node ending observe continuation node_of_above ending_of_above
  node_spin_iff)
open Minidregg.Theory.ObjectiveBendDemandCollect (checkpoint)
set_option autoImplicit false

/-- A run's own segment, read as an ending of the bounded run (the `endsWith` form). -/
theorem runSegment_yielded_ends {config : Config} {ticks : Nat} {start state : State} {plan : PlanAwait}
    (ran : runSegment config ticks start = .ok (.yielded state plan)) :
    ∃ retained extracted, endsWith (segmentLimits config start) ticks config.planBudget start =
        some (.yielded extracted.value, retained) ∧
      ObjectiveBendDemandData.yieldedPlan (segmentLimits config start) config.planBudget retained = .ok extracted ∧
      state = checkpoint extracted.state ∧ decodePlan extracted.value = .ok plan ∧
      ∃ address, runBounded (segmentLimits config start) ticks start = .yielded address retained := by
  obtain ⟨address, retained, extracted, executed, extractedExact, stored⟩ := runSegment_yielded ran
  have ends : endsWith (segmentLimits config start) ticks config.planBudget start =
      some (.yielded extracted.value, retained) := by
    simp [endsWith, executed, extractedExact]
  obtain ⟨e, y', ends', of⟩ := runSegment_ends ran
  rw [ends] at ends'
  simp only [Option.some.injEq, Prod.mk.injEq] at ends'
  obtain ⟨rfl, rfl⟩ := ends'
  exact ⟨retained, extracted, ends, extractedExact, stored, of, address, executed⟩

/-- **The lift of one segment.** A lazy state `s` in a chain with the state `t` a kernel
segment runs from: if the segment is the bounded run's own (`runSegment` committed it, under
any config and ticks), it is the reference node at `s`; and if it yielded from a lexically
valid yield, the checkpoint it stores is in a chain with the reference's own yielded state. -/
theorem segment_reference {config : Config} {ticks : Nat} {s t : State} (chain : Chain s t)
    {segment : Segment} (ran : runSegment config ticks t = .ok segment)
    (validNext : ∀ address retained, runBounded (segmentLimits config t) ticks t = .yielded address retained →
      ObjectiveBendDemandInvariant.LexicalInvariant retained) :
    ∃ e, Segment.OfEnding e segment ∧ node config.planBudget s = Node.ofEnding e ∧
      ∀ state plan, segment = .yielded state plan →
        ∃ d own, e = .yielded d ∧ decodePlan d = .ok plan ∧
          ending config.planBudget s = some (.yielded d, own) ∧ Chain own state := by
  obtain ⟨e, y', ends, of⟩ := runSegment_ends ran
  obtain ⟨y, _, above⟩ := chain.back ends
  refine ⟨e, of, node_of_above above, fun state plan yielded => ?_⟩
  subst yielded
  obtain ⟨retained, extracted, ends', extractedExact, stored, decoded, address, executed⟩ :=
    runSegment_yielded_ends ran
  rw [ends] at ends'
  simp only [Option.some.injEq, Prod.mk.injEq] at ends'
  obtain ⟨rfl, rfl⟩ := ends'
  obtain ⟨own, aboveOwn, chainOwn⟩ := chain.next ends
    (ObjectiveBendDemandForcing.addrValid_of_lexical (validNext address _ executed)) extractedExact
  subst stored
  exact ⟨extracted.value, own, rfl, decoded, ending_of_above aboveOwn, chainOwn⟩

/-! ## Birth -/

/-- The program's initial state: the reference tree's root. -/
def _root_.Minidregg.Kernel.ObjectiveActivity.Birth.start {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : BirthRequest} (birth : Birth config snapshot height request) : State :=
  initial birth.program.applied.erase

/-- Every yield of a typed program's initial run is lexically valid. -/
theorem _root_.Minidregg.Kernel.ObjectiveActivity.Birth.validYield {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : BirthRequest} (birth : Birth config snapshot height request) (ticks : Nat) :
    ∀ address retained, runBounded (segmentLimits config birth.start) ticks birth.start = .yielded address retained →
      ObjectiveBendDemandInvariant.LexicalInvariant retained := by
  intro _ retained executed
  obtain ⟨_, ⟨typed⟩⟩ := typed_runBounded_yielded
    (checked_initial_state birth.program.applied birth.program.checked) _ _ executed
  exact typed.lexical

/-- **A birth commits the reference node of the program's initial state.** Its segment is
the bounded run's own (`Birth.segmentExact`: a birth refuses every refusal, program faults
included), so it is `Node.ofEnding e` of the ending it commits. -/
theorem birth_reference {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : BirthRequest} (birth : Birth config snapshot height request) :
    ∃ e, Segment.OfEnding e birth.segment ∧ node config.planBudget birth.start = Node.ofEnding e := by
  obtain ⟨e, of, isNode, _⟩ := segment_reference
    (Chain.settles (ObjectiveBendDemandCollect.Agree.refl birth.start)) birth.segmentExact (birth.validYield _)
  exact ⟨e, of, isNode⟩

/-- **(a) A yielding birth.** The reference node of the program's initial state is `vis d`,
`d` decodes to the birth's Plan, and the checkpoint the record stores (it decodes to exactly
`state`) is in a `Chain` with the program's own yielded state, the reference's continuation
point (`ending`). -/
theorem birth_reference_vis {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : BirthRequest} (birth : Birth config snapshot height request)
    {state : State} {plan : PlanAwait} (yieldedSegment : birth.segment = .yielded state plan) :
    ∃ d own, node config.planBudget birth.start = .vis d ∧ decodePlan d = .ok plan ∧
      ending config.planBudget birth.start = some (.yielded d, own) ∧ Chain own state ∧
      decodeCheckpoint birth.record.checkpoint = some state := by
  obtain ⟨e, _, isNode, yields⟩ := segment_reference
    (Chain.settles (ObjectiveBendDemandCollect.Agree.refl birth.start)) birth.segmentExact (birth.validYield _)
  obtain ⟨d, own, rfl, decoded, ended, chain⟩ := yields state plan yieldedSegment
  exact ⟨d, own, isNode, decoded, ended, chain, (birth_checkpoint_typed birth yieldedSegment).1⟩

/-! ## Delivery -/

/-- The response term a delivery resumes its checkpoint with. -/
def _root_.Minidregg.Kernel.ObjectiveActivity.Delivery.responseTerm {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request) :
    ObjectiveBendOpenRecursion.Term :=
  (responseData delivery.settlement.decided delivery.view).term

/-- The delivery's segment is the bounded run's own. -/
def _root_.Minidregg.Kernel.ObjectiveActivity.Delivery.Ran {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request) : Prop :=
  runSegment config delivery.envelope.sourceTicks delivery.resumed = .ok delivery.segment

/-- **What a delivery commits is the bounded run's own segment, or a program fault**: the
run refused (Plan decoding, Plan or result extraction, the turn cap) or its yield commit
refused (write shape, patience), and the handler committed that refusal as `faulted`. -/
theorem _root_.Minidregg.Kernel.ObjectiveActivity.Delivery.ran_or_fault {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request) :
    delivery.Ran ∨ ∃ refusal reason, programFault config delivery.envelope.sourceTicks refusal = some reason ∧
      delivery.segment = .faulted reason ∧
      (runSegment config delivery.envelope.sourceTicks delivery.resumed = .error refusal ∨
        ∃ segment, runSegment config delivery.envelope.sourceTicks delivery.resumed = .ok segment ∧
          segmentCommit config snapshot height (deliveryTransaction delivery.await.id) request.record
            delivery.record.object (delivery.record.generation + 1) (some delivery.view) true segment =
              .error refusal) := by
  have ended := delivery.endExact
  unfold resumedSegment at ended
  split at ended
  · rename_i refusal runs
    unfold faultOr at ended
    split at ended
    · rename_i reason fault
      simp only [Except.ok.injEq, Prod.mk.injEq] at ended
      exact .inr ⟨refusal, reason, fault, ended.1.symm, .inl runs⟩
    · cases ended
  · rename_i segment runs
    split at ended
    · rename_i refusal commits
      unfold faultOr at ended
      split at ended
      · rename_i reason fault
        simp only [Except.ok.injEq, Prod.mk.injEq] at ended
        exact .inr ⟨refusal, reason, fault, ended.1.symm, .inr ⟨segment, runs, commits⟩⟩
      · cases ended
    · simp only [Except.ok.injEq, Prod.mk.injEq] at ended
      refine .inl ?_
      unfold Delivery.Ran
      rw [← ended.1]
      exact runs

/-- A yielded delivery segment is always the run's own. -/
theorem _root_.Minidregg.Kernel.ObjectiveActivity.Delivery.ran_of_yielded {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request)
    {state : State} {plan : PlanAwait} (yieldedSegment : delivery.segment = .yielded state plan) : delivery.Ran := by
  have ended := delivery.endExact
  rw [yieldedSegment] at ended
  unfold Delivery.Ran
  rw [yieldedSegment]
  exact (resumedSegment_yielded ended).1

/-- Every yield of a delivery's run is lexically valid, if its decoded checkpoint is typed
(`delivery_checkpoint_typed`'s premise). -/
theorem _root_.Minidregg.Kernel.ObjectiveActivity.Delivery.validYield {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request)
    (prior : ∃ types, Nonempty (StateTyping delivery.program.assumptions types delivery.state
      delivery.program.checked.type)) (ticks : Nat) :
    ∀ address retained, runBounded (segmentLimits config delivery.resumed) ticks delivery.resumed =
      .yielded address retained → ObjectiveBendDemandInvariant.LexicalInvariant retained := by
  intro _ retained executed
  obtain ⟨types, ⟨typed⟩⟩ := prior
  have computation := delivery.program.typeExact
  rw [computation] at typed
  obtain ⟨_, waiting⟩ := resume_requires_yield _ _ (by rw [delivery.resumeExact]; rfl)
  obtain ⟨resumedState⟩ := typed_resume_preserved typed waiting delivery.response.typed delivery.resumeExact
  obtain ⟨_, ⟨typedRetained⟩⟩ := typed_runBounded_yielded resumedState _ _ executed
  exact typedRetained.lexical

/-- **(b) A delivery against the reference.** `y` is a reference yield in a chain with the
checkpoint the delivery decoded. The reference resumes `y` with the delivered response to
`next`, in a chain with the state the delivery runs. If the delivery's segment is the bounded
run's own (`Ran`), it is the reference node at `next`; and if it yielded, the checkpoint it
stores (the next record decodes to exactly it) is in a chain with the reference's own next
yield. -/
theorem delivery_reference {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request)
    (prior : ∃ types, Nonempty (StateTyping delivery.program.assumptions types delivery.state
      delivery.program.checked.type))
    {y : State} (chain : Chain y delivery.state) :
    ∃ next, resume delivery.responseTerm y = some next ∧ Chain next delivery.resumed ∧
      (delivery.Ran → ∃ e, Segment.OfEnding e delivery.segment ∧ node config.planBudget next = Node.ofEnding e ∧
        ∀ state plan, delivery.segment = .yielded state plan →
          ∃ d own, e = .yielded d ∧ decodePlan d = .ok plan ∧
            ending config.planBudget next = some (.yielded d, own) ∧ Chain own state ∧
            decodeCheckpoint delivery.next.checkpoint = some state) := by
  obtain ⟨next, resumed, chainNext⟩ := chain.resume_back _ delivery.resumeExact
  refine ⟨next, resumed, chainNext, fun ran => ?_⟩
  obtain ⟨e, of, isNode, yields⟩ := segment_reference chainNext ran (delivery.validYield prior _)
  refine ⟨e, of, isNode, fun state plan yieldedSegment => ?_⟩
  obtain ⟨d, own, same, decoded, ended, c⟩ := yields state plan yieldedSegment
  exact ⟨d, own, same, decoded, ended, c, (delivery_checkpoint_typed delivery prior yieldedSegment).1⟩

/-- **(b), in the reference's own terms**: if the reference at `p` yields to `y`, in a chain
with the delivery's checkpoint, the delivery's own segment is the node at the continuation
`continuation p r`, which is `observe p [r]`. -/
theorem delivery_observe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request)
    (prior : ∃ types, Nonempty (StateTyping delivery.program.assumptions types delivery.state
      delivery.program.checked.type))
    {p y : State} {d : ObjectiveBendDemandData.Data} (yields : ending config.planBudget p = some (.yielded d, y))
    (chain : Chain y delivery.state) (ran : delivery.Ran) :
    ∃ next e, continuation config.planBudget p delivery.responseTerm = some next ∧
      Segment.OfEnding e delivery.segment ∧ observe config.planBudget p [delivery.responseTerm] = Node.ofEnding e := by
  obtain ⟨next, resumed, _, lift⟩ := delivery_reference delivery prior chain
  obtain ⟨e, of, isNode, _⟩ := lift ran
  refine ⟨next, e, by simp [continuation, yields, resumed], of, ?_⟩
  simp [observe, yields, resumed, isNode]

/-- **If the reference spins at the continuation, no delivery there commits a run's own
segment**, under any config and any ticks: every segment it commits is a program fault. -/
theorem delivery_spin {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request)
    {y next : State} (chain : Chain y delivery.state) (resumed : resume delivery.responseTerm y = some next)
    (spin : node config.planBudget next = .spin) (config' : Config) (ticks : Nat) (segment : Segment) :
    runSegment config' ticks delivery.resumed ≠ .ok segment := by
  intro ran
  obtain ⟨next', resumed', chainNext⟩ := chain.resume_back _ delivery.resumeExact
  change resume delivery.responseTerm y = some next' at resumed'
  rw [resumed] at resumed'
  cases resumed'
  obtain ⟨e, y', ends, _⟩ := runSegment_ends ran
  rw [chainNext.spins ((node_spin_iff _ _).mp spin) _ _ _] at ends
  cases ends

/-- **(b)'s chain premise holds at the first delivery**: a delivery that decoded the record a
yielding birth wrote decoded a checkpoint in a chain with the reference's own first yield
(`birth_reference_vis`). Later deliveries get it from the delivery before them
(`delivery_reference`'s last conjunct). -/
theorem first_delivery_chain {rootBytes : Bytes → Digest} {config : Config} {snapshot snapshot' : Snapshot rootBytes}
    {height height' : Nat} {request : BirthRequest} {deliverRequest : DeliverRequest}
    (birth : Birth config snapshot height request) {state : State} {plan : PlanAwait}
    (yieldedSegment : birth.segment = .yielded state plan)
    (delivery : Delivery config snapshot' height' deliverRequest) (same : delivery.record = birth.record) :
    ∃ d own, ending config.planBudget birth.start = some (.yielded d, own) ∧ Chain own delivery.state := by
  obtain ⟨d, own, _, _, ended, chain, decoded⟩ := birth_reference_vis birth yieldedSegment
  have read := delivery.stateExact
  rw [same, decoded] at read
  cases read
  exact ⟨d, own, ended, chain⟩

/-! ## Exhaustion -/

def _root_.Minidregg.Kernel.ObjectiveActivity.Exhaustion.responseTerm {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ExhaustRequest} (attempt : Exhaustion config snapshot height request) :
    ObjectiveBendOpenRecursion.Term :=
  (responseData attempt.settlement.decided attempt.view).term

/-- **(d) An exhaustion against the reference.** It resumes the reference yield `y` with the
same response to a state in a chain with the one it runs; its run commits no segment (it
exhausted); and the record it writes keeps the checkpoint, the generation and the await, so
the chain with `y` is unchanged for the next attempt. -/
theorem exhaustion_reference {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ExhaustRequest} (attempt : Exhaustion config snapshot height request)
    {y : State} (chain : Chain y attempt.state) :
    (∃ next, resume attempt.responseTerm y = some next ∧ Chain next attempt.resumed) ∧
      (∀ segment, runSegment config attempt.envelope.sourceTicks attempt.resumed ≠ .ok segment) ∧
      attempt.next.checkpoint = attempt.record.checkpoint ∧ attempt.next.phase = attempt.record.phase ∧
      attempt.next.generation = attempt.record.generation ∧
      decodeCheckpoint attempt.next.checkpoint = some attempt.state := by
  obtain ⟨next, resumed, chainNext⟩ := chain.resume_back _ attempt.resumeExact
  refine ⟨⟨next, resumed, chainNext⟩, fun segment ran => ?_, ?_, ?_, ?_, ?_⟩
  · rw [attempt.ran] at ran; cases ran
  · rw [attempt.nextExact]
  · rw [attempt.nextExact]
  · rw [attempt.nextExact]
  · rw [attempt.nextExact]; exact attempt.stateExact

#assert_axioms runSegment_yielded_ends
#assert_axioms segment_reference
#assert_axioms ObjectiveActivity.Birth.validYield
#assert_axioms birth_reference
#assert_axioms birth_reference_vis
#assert_axioms ObjectiveActivity.Delivery.ran_or_fault
#assert_axioms ObjectiveActivity.Delivery.ran_of_yielded
#assert_axioms ObjectiveActivity.Delivery.validYield
#assert_axioms delivery_reference
#assert_axioms delivery_observe
#assert_axioms delivery_spin
#assert_axioms first_delivery_chain
#assert_axioms exhaustion_reference

end Minidregg.Kernel.ObjectiveReferenceLift
