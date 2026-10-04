/- The kernel stores only well-typed checkpoints, and what it stores resumes as the
state it was made from (ObjectiveProofs).

`Kernel.ObjectiveActivity` stores, at a yield, the state the Plan extraction left (the
yielded control and stack over the heap in which every cell the extraction forced is
cached), settled and collected (`ObjectiveBendDemandCollect.checkpoint`), as checkpoint
bytes, and resumes it with an outcome the actual checker typed at the program's declared
response type. This module proves, from the preservation theorems
(`typed_stepRaw_preserved`, `typed_resume_preserved`, `checked_initial_state`), the
forced-state typing (`typed_checkpoint`) and the codec round trip (`state_roundTrip`):

* `birth_checkpoint_typed`: the checkpoint a birth stores decodes to exactly the
  checkpoint of its first segment's extraction, and that state is typed at the
  instantiated program's own checked type;
* `delivery_checkpoint_typed`: if the checkpoint a delivery decoded was typed (what the
  two theorems establish for every checkpoint the kernel wrote), the checkpoint it
  stores decodes to exactly its new checkpoint, again typed;
* `runSegment_checkpoint`: resuming the stored checkpoint ends every segment as
  resuming the extraction's state would (settling is an exact lockstep, collecting a
  renaming);
* `runSegment_stored_complete`: resuming the stored checkpoint ends every segment the
  program's OWN yielded state ends, alike, with heap headroom of the forced state's
  size, PROVIDED `ForcingTransparent` holds of that yield. `ForcingTransparent` is an
  open premise (sharing transparency of the extraction's forcing), named, with a
  satisfying instance (`forcingTransparent_tally`, the Tally run) and a refuting one
  (`not_forcingTransparent_lostStack`); its discharge is lane ACTIVITY-NATIVE-2's work.

So the before-root check of a kernel checkpoint is codec validity and the digest
binding (Scribe note B3): no executable machine-state checker is needed for
states the kernel produced, and no foreign checkpoint is ever admitted (a
delivery decodes only the record cell's own bytes). -/
import Kernel.ObjectiveActivity
import Theory.ObjectiveBendDemandPreservation
import Theory.ObjectiveBendCheckpointRoundTrip
import Theory.ObjectiveBendDemandForceProofs
import Theory.AssertCompiled

namespace Minidregg.Kernel.ObjectiveResumeContract
open Minidregg.Theory Minidregg.Compiler
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ObjectiveActivityWire
open Minidregg.Kernel.ObjectiveActivity
open Minidregg.Theory.ObjectiveBendTypes (Ty)
open Minidregg.Theory.ObjectiveBendTyping
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandTyping
open Minidregg.Theory.ObjectiveBendDemandPreservation
open Minidregg.Theory.ObjectiveBendDemandCollect (collect typed_collect collect_resume_segment checkpoint settle
  settle_resume_segment typed_checkpoint runBounded_yields_outside yieldedPlanWith_control)
open Minidregg.Theory.ObjectiveBendTyping (decodeTerm)
open Minidregg.Theory.ObjectiveBendOpenRecursion (Term)
set_option autoImplicit false

/-- The checkpoint bytes decode to exactly the state they encode. -/
theorem decodeCheckpoint_checkpointBytes (state : State) :
    decodeCheckpoint (checkpointBytes state) = some state := by
  unfold decodeCheckpoint
  rw [checkpointBytes_tokens]
  exact ObjectiveBendCheckpointRoundTrip.state_roundTrip state

/-- Typing survives the bounded executor up to a yield. -/
theorem typed_runBounded_yielded {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} (typed : StateTyping assumptions types state result)
    (limits : Limits) (ticks : Nat) {plan : Address} {retained : State}
    (ran : runBounded limits ticks state = .yielded plan retained) :
    ∃ after, Nonempty (StateTyping assumptions after retained result) := by
  induction ticks generalizing types state with
  | zero =>
      cases control : state.control <;> simp only [runBounded, control] at ran <;> try cases ran
      exact ⟨types, ⟨typed⟩⟩
  | succ ticks ih =>
      cases control : state.control <;> simp only [runBounded, step, control] at ran <;> try cases ran
      all_goals first
        | exact ⟨types, ⟨typed⟩⟩
        | (by_cases fits : (stepRaw state).heap.size ≤ limits.heap ∧ (stepRaw state).stack.length ≤ limits.stack
           · obtain ⟨_, _, ⟨next⟩⟩ := typed_stepRaw_preserved typed
             exact ih next (by simpa [fits] using ran)
           · simp [fits] at ran)

/-- A segment that yielded came from the bounded executor's yield, whose Plan extracted,
and stores that extraction's checkpoint. -/
theorem runSegment_yielded {config : Config} {ticks : Nat} {start state : State} {plan : PlanAwait}
    (ran : runSegment config ticks start = .ok (.yielded state plan)) :
    ∃ address retained extracted, runBounded config.limits ticks start = .yielded address retained ∧
      ObjectiveBendDemandData.yieldedPlan config.limits config.planBudget retained = .ok extracted ∧
      state = checkpoint extracted.state := by
  unfold runSegment at ran
  split at ran
  · rename_i address yielded equation
    split at ran
    · rename_i extracted extractedExact
      simp only [bind, Except.bind] at ran
      split at ran
      · cases ran
      · cases ran; exact ⟨address, yielded, extracted, equation, extractedExact, rfl⟩
    · cases ran
  · split at ran <;> cases ran
  · cases ran
  · cases ran
  · cases ran

/-- A yielded segment's commit always exists when it was admitted. -/
theorem segmentCommit_yielded {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {transaction : TransactionId} {cell object : CellId}
    {generation : Nat} {current : Option ObjectState} {viewed : Bool} {state : State} {plan : PlanAwait}
    {committed : Option YieldCommit}
    (ok : segmentCommit config snapshot height transaction cell object generation current viewed
      (.yielded state plan) = .ok committed) :
    ∃ yielded, committed = some yielded := by
  simp only [segmentCommit, bind, Except.bind] at ok
  split at ok
  · cases ok
  · simp only [pure, Except.pure, Except.ok.injEq] at ok
    exact ⟨_, ok.symm⟩

/-- The record that ends a yielded segment stores exactly its yielded state. -/
theorem nextRecord_checkpoint (base : Record) (generation : Nat) (state : State)
    (plan : PlanAwait) (yielded : YieldCommit) :
    (nextRecord base generation (.yielded state plan) (some yielded)).checkpoint =
      checkpointBytes state := rfl

/-- **A birth stores a well-typed checkpoint.** -/
theorem birth_checkpoint_typed {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : BirthRequest} (birth : Birth config snapshot height request)
    {state : State} {plan : PlanAwait} (yieldedSegment : birth.segment = .yielded state plan) :
    decodeCheckpoint birth.record.checkpoint = some state ∧
      ∃ types, Nonempty (StateTyping birth.program.assumptions types state birth.program.checked.type) := by
  have commit := birth.yieldedExact
  rw [yieldedSegment] at commit
  obtain ⟨yielded, someYielded⟩ := segmentCommit_yielded commit
  refine ⟨?_, ?_⟩
  · rw [birth.recordExact, yieldedSegment, someYielded, nextRecord_checkpoint]
    exact decodeCheckpoint_checkpointBytes state
  · have ran := birth.segmentExact
    rw [yieldedSegment] at ran
    obtain ⟨_, retained, extracted, executed, extractedExact, stored⟩ := runSegment_yielded ran
    obtain ⟨_, ⟨typed⟩⟩ := typed_runBounded_yielded
      (checked_initial_state birth.program.applied birth.program.checked) config.limits request.envelope.sourceTicks executed
    have outside := runBounded_yields_outside config.limits request.envelope.sourceTicks _
      (fun p h => by simp [initial] at h) executed
    subst stored
    exact typed_checkpoint typed outside extractedExact

/-- **A delivery stores a well-typed checkpoint.** If the checkpoint it decoded
from the record cell was typed at the program's checked type (as every
checkpoint a birth or a delivery stores is), the response it resumed with is
typed by the actual checker at the program's response type, so the resumed
state is typed (`typed_resume_preserved`), the segment keeps it typed, and the
record it stores decodes to exactly that state. -/
theorem delivery_checkpoint_typed {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : DeliverRequest}
    (delivery : Delivery config snapshot height request)
    (prior : ∃ types, Nonempty (StateTyping delivery.program.assumptions types delivery.state
      delivery.program.checked.type))
    {state : State} {plan : PlanAwait} (yieldedSegment : delivery.segment = .yielded state plan) :
    decodeCheckpoint delivery.next.checkpoint = some state ∧
      ∃ types, Nonempty (StateTyping delivery.program.assumptions types state delivery.program.checked.type) := by
  have commit := delivery.yieldedExact
  rw [yieldedSegment] at commit
  obtain ⟨yielded, someYielded⟩ := segmentCommit_yielded commit
  refine ⟨?_, ?_⟩
  · rw [delivery.nextExact, yieldedSegment, someYielded, nextRecord_checkpoint]
    exact decodeCheckpoint_checkpointBytes state
  · obtain ⟨types, ⟨typed⟩⟩ := prior
    have computation := delivery.program.typeExact
    rw [computation] at typed
    obtain ⟨address, waiting⟩ := resume_requires_yield _ _ (by rw [delivery.resumeExact]; rfl)
    have resumedTyped := typed_resume_preserved typed waiting delivery.response.typed delivery.resumeExact
    obtain ⟨resumedState⟩ := resumedTyped
    have ran := delivery.segmentExact
    rw [yieldedSegment] at ran
    obtain ⟨_, retained, extracted, executed, extractedExact, stored⟩ := runSegment_yielded ran
    rw [computation]
    obtain ⟨_, ⟨typedRetained⟩⟩ := typed_runBounded_yielded resumedState config.limits delivery.envelope.sourceTicks executed
    have evaluating := (resume_keeps_heap_and_stack _ _ _ delivery.resumeExact).2.2
    have outside := runBounded_yields_outside config.limits delivery.envelope.sourceTicks _
      (fun p h => by rw [evaluating] at h; cases h) executed
    subst stored
    exact typed_checkpoint typedRetained outside extractedExact

/-- Two segments end alike: the same Plan, the same result, the same fault. -/
def Segment.Agrees : Segment → Segment → Prop
  | .yielded _ plan, .yielded _ plan' => plan.write = plan'.write ∧ plan.source = plan'.source ∧
      plan.patience = plan'.patience
  | .finished result, .finished result' => result = result'
  | .faulted reason, .faulted reason' => reason = reason'
  | _, _ => False

theorem Segment.Agrees.trans {a b c : Segment} (one : Segment.Agrees a b) (two : Segment.Agrees b c) :
    Segment.Agrees a c := by
  cases a <;> cases b <;> cases c <;> simp_all [Segment.Agrees]

/-- A segment transfers between two resumed states whose bounded runs correspond:
every yield whose Plan extracts has a yield whose Plan extracts to the same Data, every
completion a completion to the same Data, every divergence a divergence, every refusal
the same refusal. -/
theorem runSegment_transfer {config : Config} {ticks : Nat} {s t : State}
    (yields : ∀ plan y r, runBounded config.limits ticks s = .yielded plan y →
      ObjectiveBendDemandData.yieldedPlan config.limits config.planBudget y = .ok r →
      ∃ plan' y' r', runBounded config.limits ticks t = .yielded plan' y' ∧
        ObjectiveBendDemandData.yieldedPlan config.limits config.planBudget y' = .ok r' ∧ r'.value = r.value)
    (finishes : ∀ value y r, runBounded config.limits ticks s = .finished value y →
      ObjectiveBendDemandData.complete config.limits config.planBudget y = .ok r →
      ∃ value' y' r', runBounded config.limits ticks t = .finished value' y' ∧
        ObjectiveBendDemandData.complete config.limits config.planBudget y' = .ok r' ∧ r'.value = r.value)
    (diverges : ∀ address y, runBounded config.limits ticks s = .divergent address y →
      ∃ address' y', runBounded config.limits ticks t = .divergent address' y')
    (refuses : ∀ reason y, runBounded config.limits ticks s = .refused reason y →
      ∃ y', runBounded config.limits ticks t = .refused reason y')
    {segment : Segment} (ran : runSegment config ticks s = .ok segment) :
    ∃ segment', runSegment config ticks t = .ok segment' ∧ Segment.Agrees segment segment' := by
  unfold runSegment at ran
  split at ran
  · rename_i address retained equation
    split at ran
    · rename_i extracted extractedExact
      simp only [bind, Except.bind] at ran
      split at ran
      · cases ran
      · rename_i plan decoded
        cases ran
        obtain ⟨_, y', r', run', extracted', same⟩ := yields address retained extracted equation extractedExact
        refine ⟨.yielded (checkpoint r'.state) plan, ?_, ⟨rfl, rfl, rfl⟩⟩
        unfold runSegment
        rw [run']
        simp only [extracted', same, decoded, bind, Except.bind, pure, Except.pure]
    · cases ran
  · rename_i value retained equation
    split at ran
    · rename_i result resultExact
      cases ran
      obtain ⟨_, y', r', run', complete', same⟩ := finishes value retained result equation resultExact
      refine ⟨.finished r'.value, ?_, same.symm⟩
      unfold runSegment
      rw [run']
      simp only [complete']
    · cases ran
  · rename_i address retained equation
    cases ran
    obtain ⟨_, y', run'⟩ := diverges address retained equation
    refine ⟨.faulted "divergent", ?_, rfl⟩
    unfold runSegment
    rw [run']
  · rename_i reason retained equation
    cases ran
    obtain ⟨y', run'⟩ := refuses reason retained equation
    refine ⟨.faulted (reprStr reason), ?_, rfl⟩
    unfold runSegment
    rw [run']
  · cases ran

/-- **What the kernel stores resumes as the extraction's state.** Whatever a segment
resumed from the state the Plan extraction left commits, the segment resumed from the
stored checkpoint (that state settled, then collected) commits alike: the same next Plan
(state, source, patience), the same result, the same fault. Settling is an exact
lockstep; collecting is a renaming whose heap is no larger. -/
theorem runSegment_checkpoint {config : Config} {ticks : Nat} {forced resumed : State} {response : Term}
    (yielded : resume response forced = some resumed) {segment : Segment}
    (ran : runSegment config ticks resumed = .ok segment) :
    ∃ resumed' segment', resume response (checkpoint forced) = some resumed' ∧
      runSegment config ticks resumed' = .ok segment' ∧ Segment.Agrees segment segment' := by
  obtain ⟨settled, settledResume, sy, sf, sd, sr⟩ :=
    settle_resume_segment yielded config.limits ticks config.planBudget
  obtain ⟨seg1, ran1, agree1⟩ := runSegment_transfer (s := resumed) (t := settled)
    (fun plan y r h1 h2 => by
      obtain ⟨y', r', a, _, b, c⟩ := sy plan y r h1 h2; exact ⟨plan, y', r', a, b, c.1⟩)
    (fun value y r h1 h2 => by obtain ⟨y', r', a, b, c⟩ := sf value y r h1 h2; exact ⟨value, y', r', a, b, c⟩)
    (fun a y h => by obtain ⟨y', h'⟩ := sd a y h; exact ⟨a, y', h'⟩)
    sr ran
  obtain ⟨collected, collectedResume, cy, cf, cd, cr⟩ :=
    collect_resume_segment settledResume config.limits ticks config.planBudget
  obtain ⟨seg2, ran2, agree2⟩ := runSegment_transfer (s := settled) (t := collected)
    (fun plan y r h1 h2 => by
      obtain ⟨y', r', a, _, b, c⟩ := cy plan y r h1 h2; exact ⟨_, y', r', a, b, c⟩)
    (fun value y r h1 h2 => by obtain ⟨y', r', a, b, c⟩ := cf value y r h1 h2; exact ⟨_, y', r', a, b, c⟩)
    (fun a y h => by obtain ⟨y', h'⟩ := cd a y h; exact ⟨_, y', h'⟩)
    cr ran1
  exact ⟨collected, seg2, collectedResume, ran2, agree1.trans agree2⟩

/-! ## The open premise: the extraction's forcing is transparent -/

/-- The configuration with heap headroom of `forced`'s size. -/
def headroom (config : Config) (forced : State) : Config :=
  {config with limits := ⟨config.limits.heap + forced.heap.size, config.limits.stack⟩}

/-- **Open premise (sharing transparency of Plan extraction); NOT proved here.**

`yielded` is the machine's own yielded state, `forced` the state its Plan extraction
left (the same control and stack, every cell the extraction forced cached). Assumed:
whatever segment resuming `yielded` with `response` ends under `config` and `ticks`,
resuming `forced` with the same response ends ALIKE (`Segment.Agrees`: the same Plan,
result or fault), under the same ticks and stack, with heap headroom of `forced`'s size
(`headroom`).

The headroom is not slack: forcing can make a checkpoint LARGER
(`ObjectiveBendDemandCollect.largerYield_checkpoint_grows`: 2 cells unforced, 5
forced), so the forced resume can run out of heap where the unforced one would not.
Ticks and stack need none (the forced run skips work and update frames; it never adds
any).

Why it should hold: the machine is deterministic and a cached value is what its thunk
evaluates to; forcing early only moves work. Why it is not yet a theorem: the proof is
a stuttering simulation up to a growing address correspondence (closed demands commute),
lane ACTIVITY-NATIVE-2's open obligation. Evidence: `forcingTransparent_tally` (a
satisfying instance, by compiled evaluation), `not_forcingTransparent_lostStack` (a
refuting one), and the executed differential
`scripts/check-objective-proofs.sh transparency` over every activity of the preview
cohort and the Tally run. -/
def ForcingTransparent (config : Config) (yielded forced : State) (response : Term) (ticks : Nat) : Prop :=
  ∀ (s0 t0 : State) (segment : Segment), resume response yielded = some s0 → resume response forced = some t0 →
    runSegment config ticks s0 = .ok segment →
    ∃ segment', runSegment (headroom config forced) ticks t0 = .ok segment' ∧ Segment.Agrees segment segment'

/-- **What the kernel stores ends every segment the program's own yield ends**, alike,
with heap headroom of the forced state's size, given `ForcingTransparent` of that yield.
The stored checkpoint is the extraction's state settled and collected
(`runSegment_checkpoint`); the extraction's state against the yield is the premise. -/
theorem runSegment_stored_complete {config : Config} {ticks : Nat} {yielded resumed : State}
    {response : Term} {extracted : ObjectiveBendDemandData.Result}
    (found : ObjectiveBendDemandData.yieldedPlan config.limits config.planBudget yielded = .ok extracted)
    (transparent : ForcingTransparent config yielded extracted.state response ticks)
    (resumedExact : resume response yielded = some resumed) {segment : Segment}
    (ran : runSegment config ticks resumed = .ok segment) :
    ∃ stored segment', resume response (checkpoint extracted.state) = some stored ∧
      runSegment (headroom config extracted.state) ticks stored = .ok segment' ∧
      Segment.Agrees segment segment' := by
  have sameControl := (yieldedPlanWith_control found).1
  obtain ⟨plan, isYielded⟩ := resume_requires_yield response yielded (by rw [resumedExact]; rfl)
  have forcedResume : resume response extracted.state =
      some {extracted.state with control := .evaluate response []} := by
    simp [resume, sameControl, isYielded]
  obtain ⟨seg1, ran1, agree1⟩ := transparent resumed _ segment resumedExact forcedResume ran
  obtain ⟨stored, seg2, storedResume, ran2, agree2⟩ := runSegment_checkpoint forcedResume ran1
  exact ⟨stored, seg2, storedResume, ran2, agree1.trans agree2⟩

/-! ### Deciding the premise at one point -/

open Minidregg.Theory.ObjectiveBendDemandData (Data)

mutual
def dataBeq : Data → Data → Bool
  | .natural a, .natural b => a == b
  | .boolean a, .boolean b => a == b
  | .label a, .label b => a == b
  | .record fs, .record gs => fieldsBeq fs gs
  | .variant l p, .variant l2 p2 => l == l2 && dataBeq p p2
  | _, _ => false
def fieldsBeq : List (String × Data) → List (String × Data) → Bool
  | [], [] => true
  | (n, d) :: r, (n2, d2) :: r2 => n == n2 && dataBeq d d2 && fieldsBeq r r2
  | _, _ => false
end

mutual
theorem dataBeq_sound : (a b : Data) → dataBeq a b = true → a = b
  | .natural x, .natural y, h => by simp [dataBeq] at h; rw [h]
  | .boolean x, .boolean y, h => by simp [dataBeq] at h; rw [h]
  | .label x, .label y, h => by simp [dataBeq] at h; rw [h]
  | .record fs, .record gs, h => by rw [fieldsBeq_sound fs gs (by simpa [dataBeq] using h)]
  | .variant l p, .variant l2 p2, h => by
      simp only [dataBeq, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1, dataBeq_sound p p2 h.2]
  | .natural _, .boolean _, h | .natural _, .label _, h | .natural _, .record _, h | .natural _, .variant _ _, h
  | .boolean _, .natural _, h | .boolean _, .label _, h | .boolean _, .record _, h | .boolean _, .variant _ _, h
  | .label _, .natural _, h | .label _, .boolean _, h | .label _, .record _, h | .label _, .variant _ _, h
  | .record _, .natural _, h | .record _, .boolean _, h | .record _, .label _, h | .record _, .variant _ _, h
  | .variant _ _, .natural _, h | .variant _ _, .boolean _, h | .variant _ _, .label _, h | .variant _ _, .record _, h =>
      by simp [dataBeq] at h
theorem fieldsBeq_sound : (fs gs : List (String × Data)) → fieldsBeq fs gs = true → fs = gs
  | [], [], _ => rfl
  | (n, d) :: r, (n2, d2) :: r2, h => by
      simp only [fieldsBeq, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1.1, dataBeq_sound d d2 h.1.2, fieldsBeq_sound r r2 h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [fieldsBeq] at h
end

mutual
theorem dataBeq_refl : (a : Data) → dataBeq a a = true
  | .natural x => by simp [dataBeq]
  | .boolean x => by simp [dataBeq]
  | .label x => by simp [dataBeq]
  | .record fs => by simp only [dataBeq]; exact fieldsBeq_refl fs
  | .variant l p => by simp only [dataBeq, beq_self_eq_true, Bool.true_and]; exact dataBeq_refl p
theorem fieldsBeq_refl : (fs : List (String × Data)) → fieldsBeq fs fs = true
  | [] => rfl
  | (n, d) :: r => by
      simp only [fieldsBeq, beq_self_eq_true, Bool.true_and]
      rw [dataBeq_refl d, fieldsBeq_refl r]; rfl
end

@[simp] theorem dataBeq_iff (a b : Data) : dataBeq a b = true ↔ a = b :=
  ⟨dataBeq_sound a b, fun same => same ▸ dataBeq_refl a⟩

def Segment.agreesB : Segment → Segment → Bool
  | .yielded _ plan, .yielded _ plan' =>
    dataBeq plan.write plan'.write && decide (plan.source = plan'.source) && plan.patience == plan'.patience
  | .finished result, .finished result' => dataBeq result result'
  | .faulted reason, .faulted reason' => reason == reason'
  | _, _ => false

theorem Segment.agreesB_iff (a b : Segment) : Segment.agreesB a b = true ↔ Segment.Agrees a b := by
  cases a <;> cases b <;> simp [Segment.agreesB, Segment.Agrees, and_assoc]

/-- The premise at one point, decided by running both resumptions. -/
def forcingTransparentCheck (config : Config) (yielded forced : State) (response : Term) (ticks : Nat) : Bool :=
  match resume response yielded, resume response forced with
  | some s0, some t0 =>
    match runSegment config ticks s0 with
    | .ok segment =>
      match runSegment (headroom config forced) ticks t0 with
      | .ok segment' => Segment.agreesB segment segment'
      | .error _ => false
    | .error _ => true
  | _, _ => true

theorem forcingTransparent_of_check {config : Config} {yielded forced : State} {response : Term} {ticks : Nat}
    (checked : forcingTransparentCheck config yielded forced response ticks = true) :
    ForcingTransparent config yielded forced response ticks := by
  intro s0 t0 segment hs ht ran
  simp only [forcingTransparentCheck, hs, ht, ran] at checked
  split at checked
  · rename_i segment' ran'
    exact ⟨segment', ran', (Segment.agreesB_iff _ _).mp checked⟩
  · cases checked

/-- A point where the premise fails, decided by running both resumptions. -/
def forcingOpaqueCheck (config : Config) (yielded forced : State) (response : Term) (ticks : Nat) : Bool :=
  match resume response yielded, resume response forced with
  | some s0, some t0 =>
    match runSegment config ticks s0 with
    | .ok segment =>
      match runSegment (headroom config forced) ticks t0 with
      | .ok segment' => !Segment.agreesB segment segment'
      | .error _ => true
    | .error _ => false
  | _, _ => false

theorem not_forcingTransparent_of_refute {config : Config} {yielded forced : State} {response : Term} {ticks : Nat}
    (checked : forcingOpaqueCheck config yielded forced response ticks = true) :
    ¬ ForcingTransparent config yielded forced response ticks := by
  intro transparent
  unfold forcingOpaqueCheck at checked
  split at checked
  · rename_i s0 t0 hs ht
    split at checked
    · rename_i segment ran
      obtain ⟨segment', ran', agree⟩ := transparent s0 t0 segment hs ht ran
      rw [ran'] at checked
      have := (Segment.agreesB_iff _ _).mpr agree
      simp [this] at checked
    · cases checked
  · cases checked

/-! ### The Tally run: a satisfying and a refuting point

`tests/objective-activity/TallyTwelve.core.json` is the Tally activity
(world/activity/Tally.obend, `tally {init: set 0, decider: 9}`) as the pinned front end and
elaborator emit it (`native/objective-emit/packets.ts` over
`native/objective-emit/activity-cohort.json`); `scripts/check-objective-proofs.sh
transparency` re-elaborates it and requires the committed bytes. -/

def tallyCore : String := include_str ".." / "tests" / "objective-activity" / "TallyTwelve.core.json"

def tallyTerm : Term :=
  match Lean.Json.parse tallyCore >>= (·.getObjVal? "term") >>= decodeTerm 4096 with
  | .ok term => term
  | .error _ => .nat 0

def tallyConfig : Config where
  deployment := ⟨⟨1⟩, 2, 3, 4⟩
  asset := 0
  collector := 0
  limits := ⟨100000, 100000⟩
  planBudget := ⟨10000, 100000, 1048576⟩
  maxTicks := 200000
  maxPatience := 16
  typeFuel := 16384
  maxArtifactBytes := 4194304
  tariff := ⟨Minidregg.Kernel.ObjectiveTariff.tariffVersion, 10, 0, 1, 0, 0, 0, 0, 0⟩
  abandonGrace := 16

/-- Tally's first yield (it awaits a reply with its total 0). -/
def tallyYield : State :=
  match runBounded tallyConfig.limits 200000 (initial tallyTerm) with
  | .yielded _ yielded => yielded
  | _ => initial tallyTerm

def tallyForced : State :=
  match ObjectiveBendDemandData.yieldedPlan tallyConfig.limits tallyConfig.planBudget tallyYield with
  | .ok extracted => extracted.state
  | .error _ => tallyYield

/-- The first resume: a reply of 5, with the view the birth wrote (version 1, total 0). -/
def tallyReply : Term :=
  (Data.variant "resumed" (.record [("outcome", .variant "reply" (.record [("amount", .natural 5)])),
    ("view", .record [("version", .natural 1), ("state", .record [("total", .natural 0)])])])).term

/-- **Satisfying point**: resumed with a reply, Tally's forced first yield ends its next
segment (a yield publishing 5) as its own yield does. -/
theorem forcingTransparent_tally : ForcingTransparent tallyConfig tallyYield tallyForced tallyReply 200000 :=
  forcingTransparent_of_check (by native_decide)

/-- **Refuting point**: a "forced" state that lost its continuation (the stack) is not
transparent: resumed, it finishes with the reply where the yield yields again. -/
theorem not_forcingTransparent_lostStack :
    ¬ ForcingTransparent tallyConfig tallyYield {tallyForced with stack := []} tallyReply 200000 :=
  not_forcingTransparent_of_refute (by native_decide)

#assert_axioms decodeCheckpoint_checkpointBytes
#assert_axioms typed_runBounded_yielded
#assert_axioms runSegment_yielded
#assert_axioms segmentCommit_yielded
#assert_axioms birth_checkpoint_typed
#assert_axioms delivery_checkpoint_typed
#assert_axioms Segment.Agrees.trans
#assert_axioms runSegment_transfer
#assert_axioms runSegment_checkpoint
#assert_axioms runSegment_stored_complete
#assert_axioms dataBeq_sound
#assert_axioms dataBeq_refl
#assert_axioms Segment.agreesB_iff
#assert_axioms forcingTransparent_of_check
#assert_axioms not_forcingTransparent_of_refute
#assert_compiled forcingTransparent_tally
#assert_compiled not_forcingTransparent_lostStack
end Minidregg.Kernel.ObjectiveResumeContract
