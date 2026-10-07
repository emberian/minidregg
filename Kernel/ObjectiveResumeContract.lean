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
* `forcingTransparent_of_yieldedPlan`: resuming the state a successful Plan extraction
  left ends every segment resuming the yielded state ends, alike, under the kernel's own
  limits (`segmentLimits`: counted from each segment's own heap end), for every yield that
  names only allocated addresses (`LexicalInvariant`, which every typed state has). Proof:
  the extraction is a chain of finished closed demands, each a forcing chain
  (`ObjectiveBendDemandForcingDemand.demand_forces`), and along a chain the forced run does
  whatever the lazy run does given room for the cells the chain added
  (`ObjectiveBendDemandForcingExtract.forces_segment`), which counting from the forced
  state's heap end grants. Without the premise the statement is FALSE
  (`not_forcingTransparent_dangling`, below);
* `runSegment_stored_complete`: resuming the stored checkpoint ends every segment the
  program's OWN yielded state ends, alike, under the kernel's own limits, for every lexically
  valid yield. Under limits counted from zero it is FALSE (`absolute_limits_refuted`); the
  converse is FALSE in both resources (`stored_commits_where_lazy_exhausts`,
  `stored_commits_where_lazy_extraction_fails`: the cache saves ticks and budget);
* `birth_stored_complete`, `delivery_stored_complete` (and, in
  `Kernel.ObjectiveCheckpointInvariant`, `reachable_delivery_stored_complete`): for every
  checkpoint the kernel stores, with no premise beyond the one the typing invariant
  already discharges, the stored state is the checkpoint of the yield the segment's own run
  retained, and resumes as that yield (`StoredComplete`);
* `Delivery.spend`, `Exhaustion.spend`, `SpendDeclared.priced`: every component a resumed run
  may spend (heap past the checkpoint, stack, ticks, output nodes and bytes, extraction ticks)
  is declared by its envelope and charged by the envelope's price;
* `runSegment_stored_converse` (with `ResourcesOnly`) and `runSegment_stored_next`: the
  converse, resources only, and the continuation states after a stored yield.

So the before-root check of a kernel checkpoint is codec validity and the digest
binding (Scribe note B3): no executable machine-state checker is needed for
states the kernel produced, and no foreign checkpoint is ever admitted (a
delivery decodes only the record cell's own bytes). -/
import Kernel.ObjectiveActivity
import Theory.ObjectiveBendDemandPreservation
import Theory.ObjectiveBendCheckpointRoundTrip
import Theory.ObjectiveBendDemandForceProofs
import Theory.AssertCompiled
import Theory.ObjectiveBendDemandForcingExtract
import Theory.ObjectiveBendInteraction

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
open Minidregg.Theory.ObjectiveBendDemandCollect (collect collect_heap_le typed_collect collect_resume_segment checkpoint settle
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
    ∃ address retained extracted, runBounded (segmentLimits config start) ticks start = .yielded address retained ∧
      ObjectiveBendDemandData.yieldedPlan (segmentLimits config start) config.planBudget retained = .ok extracted ∧
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
      (checked_initial_state birth.program.applied birth.program.checked) _ _ executed
    have outside := runBounded_yields_outside _ _ _
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
  have ended := delivery.endExact
  rw [yieldedSegment] at ended
  obtain ⟨ran, commit⟩ := resumedSegment_yielded ended
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
    obtain ⟨_, retained, extracted, executed, extractedExact, stored⟩ := runSegment_yielded ran
    rw [computation]
    obtain ⟨_, ⟨typedRetained⟩⟩ := typed_runBounded_yielded resumedState _ _ executed
    have evaluating := (resume_keeps_heap_and_stack _ _ _ delivery.resumeExact).2.2
    have outside := runBounded_yields_outside _ _ _
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

theorem Segment.Agrees.symm {a b : Segment} (agree : Segment.Agrees a b) : Segment.Agrees b a := by
  cases a <;> cases b <;> simp only [Segment.Agrees] at agree ⊢
  · exact ⟨agree.1.symm, agree.2.1.symm, agree.2.2.symm⟩
  · exact agree.symm
  · exact agree.symm

theorem Segment.Agrees.trans {a b c : Segment} (one : Segment.Agrees a b) (two : Segment.Agrees b c) :
    Segment.Agrees a c := by
  cases a <;> cases b <;> cases c <;> simp_all [Segment.Agrees]

/-- Two states with heaps of one size run their segments under the same limits. -/
theorem segmentLimits_of_size {config : Config} {s t : State} (same : s.heap.size = t.heap.size) :
    segmentLimits config s = segmentLimits config t := by
  simp only [segmentLimits, ObjectiveBendDemandCollect.limitsPast, same]

/-- A segment transfers between two resumed states whose bounded runs, each under its own
`segmentLimits`, correspond: every yield whose Plan extracts has a yield whose Plan extracts
to the same Data, every completion a completion to the same Data, every divergence a
divergence, every refusal the same refusal. -/
theorem runSegment_transfer {config : Config} {ticks : Nat} {s t : State}
    (yields : ∀ plan y r, runBounded (segmentLimits config s) ticks s = .yielded plan y →
      ObjectiveBendDemandData.yieldedPlan (segmentLimits config s) config.planBudget y = .ok r →
      ∃ plan' y' r', runBounded (segmentLimits config t) ticks t = .yielded plan' y' ∧
        ObjectiveBendDemandData.yieldedPlan (segmentLimits config t) config.planBudget y' = .ok r' ∧
        r'.value = r.value)
    (finishes : ∀ value y r, runBounded (segmentLimits config s) ticks s = .finished value y →
      ObjectiveBendDemandData.complete (segmentLimits config s) config.planBudget y = .ok r →
      ∃ value' y' r', runBounded (segmentLimits config t) ticks t = .finished value' y' ∧
        ObjectiveBendDemandData.complete (segmentLimits config t) config.planBudget y' = .ok r' ∧
        r'.value = r.value)
    (diverges : ∀ address y, runBounded (segmentLimits config s) ticks s = .divergent address y →
      ∃ address' y', runBounded (segmentLimits config t) ticks t = .divergent address' y')
    (refuses : ∀ reason y, runBounded (segmentLimits config s) ticks s = .refused reason y →
      ∃ y', runBounded (segmentLimits config t) ticks t = .refused reason y')
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
stored checkpoint (that state settled, then collected) commits alike, each under its own
`segmentLimits`: the same next Plan (state, source, patience), the same result, the same
fault. Settling is an exact lockstep on a heap of the same size; collecting is a renaming
whose heap is smaller by exactly the cells it freed, and the collected segment's limits
are counted from its own heap end, so it has the same room (`RoomFor`). -/
theorem runSegment_checkpoint {config : Config} {ticks : Nat} {forced resumed : State} {response : Term}
    (yielded : resume response forced = some resumed) {segment : Segment}
    (ran : runSegment config ticks resumed = .ok segment) :
    ∃ resumed' segment', resume response (checkpoint forced) = some resumed' ∧
      runSegment config ticks resumed' = .ok segment' ∧ Segment.Agrees segment segment' := by
  have forcedHeap := (resume_keeps_heap_and_stack _ _ _ yielded).1
  obtain ⟨settled, settledResume, sy, sf, sd, sr⟩ :=
    settle_resume_segment yielded (segmentLimits config resumed) ticks config.planBudget
  have settledHeap := (resume_keeps_heap_and_stack _ _ _ settledResume).1
  have sameLimits : segmentLimits config settled = segmentLimits config resumed :=
    segmentLimits_of_size (by rw [settledHeap, forcedHeap, ObjectiveBendDemandCollect.settle_size])
  obtain ⟨seg1, ran1, agree1⟩ := runSegment_transfer (s := resumed) (t := settled)
    (fun plan y r h1 h2 => by
      obtain ⟨y', r', a, _, b, c⟩ := sy plan y r h1 h2; rw [sameLimits]; exact ⟨plan, y', r', a, b, c.1⟩)
    (fun value y r h1 h2 => by
      obtain ⟨y', r', a, b, c⟩ := sf value y r h1 h2; rw [sameLimits]; exact ⟨value, y', r', a, b, c⟩)
    (fun a y h => by obtain ⟨y', h'⟩ := sd a y h; rw [sameLimits]; exact ⟨a, y', h'⟩)
    (fun reason y h => by obtain ⟨y', h'⟩ := sr reason y h; rw [sameLimits]; exact ⟨y', h'⟩) ran
  have heapRoom : (segmentLimits config settled).heap ≤
      (segmentLimits config (collect (settle forced))).heap +
        ((settle forced).heap.size - (collect (settle forced)).heap.size) := by
    have le := collect_heap_le (settle forced)
    simp only [segmentLimits, ObjectiveBendDemandCollect.limitsPast]
    rw [settledHeap]
    omega
  obtain ⟨collected, collectedResume, cy, cf, cd, cr⟩ :=
    collect_resume_segment settledResume (segmentLimits config settled)
      (segmentLimits config (collect (settle forced))) heapRoom (Nat.le_refl _) ticks config.planBudget
  have collectedLimits : segmentLimits config collected = segmentLimits config (collect (settle forced)) :=
    segmentLimits_of_size (by rw [(resume_keeps_heap_and_stack _ _ _ collectedResume).1])
  obtain ⟨seg2, ran2, agree2⟩ := runSegment_transfer (s := settled) (t := collected)
    (fun plan y r h1 h2 => by
      obtain ⟨y', r', a, _, b, c⟩ := cy plan y r h1 h2; rw [collectedLimits]; exact ⟨_, y', r', a, b, c⟩)
    (fun value y r h1 h2 => by
      obtain ⟨y', r', a, b, c⟩ := cf value y r h1 h2; rw [collectedLimits]; exact ⟨_, y', r', a, b, c⟩)
    (fun a y h => by obtain ⟨y', h'⟩ := cd a y h; rw [collectedLimits]; exact ⟨_, y', h'⟩)
    (fun reason y h => by obtain ⟨y', h'⟩ := cr reason y h; rw [collectedLimits]; exact ⟨y', h'⟩) ran1
  exact ⟨collected, seg2, collectedResume, ran2, agree1.trans agree2⟩

/-! ## The extraction's forcing is transparent -/

/-- **Sharing transparency, at one yield.**

`yielded` is the machine's own yielded state and `other` a state to resume in its place
(the state its Plan extraction left, or the checkpoint stored from it). The statement:
whatever segment resuming `yielded` with `response` ends under `config` and `ticks`,
resuming `other` with the same response ends ALIKE (`Segment.Agrees`: the same Plan, result
or fault), under the same config and ticks. There is no headroom: the kernel runs every
segment under its `segmentLimits`, counted from the segment's own heap end, so a forced
state's extra cells (`ObjectiveBendDemandCollect.largerYield_checkpoint_grows`: 2 cells
unforced, 5 forced) do not eat its room. Under limits counted from zero the statement is
FALSE of the kernel's own checkpoints (`absolute_limits_refuted`).

It was first stated as a premise to hold of every yield whose Plan extracts. That is FALSE:
`not_forcingTransparent_dangling` (below) is a successful extraction at which it fails, a
yield whose stack names an address past its heap. It HOLDS at every yield that names only
allocated addresses (`forcingTransparent_of_yieldedPlan`, premise `LexicalInvariant
yielded`, which every typed state has, so every yield the kernel stores). The premise has
named poles: `lexicalInvariant_initialNat` satisfies it, `not_lexicalInvariant_danglingYield`
refutes it. -/
def ForcingTransparent (config : Config) (yielded other : State) (response : Term) (ticks : Nat) : Prop :=
  ∀ (s0 t0 : State) (segment : Segment), resume response yielded = some s0 → resume response other = some t0 →
    runSegment config ticks s0 = .ok segment →
    ∃ segment', runSegment config ticks t0 = .ok segment' ∧ Segment.Agrees segment segment'

/-- **The extraction's forcing is transparent at every lexically valid yield.** The
extraction (under any limits and budget) is a chain of finished closed demands; the yielded
heap forces to the extraction's heap along it (`yieldedPlan_forces`), on the resumed control
and the yield's stack; and along a forcing chain the forced run ends every segment the lazy
run ends, alike, given heap room of the cells the chain added (`forces_segment`), which is
exactly what counting the forced segment's limits from its own heap end gives it. -/
theorem forcingTransparent_of_yieldedPlan {config : Config} {limits : Limits}
    {budget : ObjectiveBendDemandData.Budget} {yielded : State} {extracted : ObjectiveBendDemandData.Result}
    (valid : ObjectiveBendDemandInvariant.LexicalInvariant yielded)
    (found : ObjectiveBendDemandData.yieldedPlan limits budget yielded = .ok extracted)
    (response : Term) (ticks : Nat) : ForcingTransparent config yielded extracted.state response ticks := by
  intro s0 t0 segment hs ht ran
  have addr := ObjectiveBendDemandForcing.addrValid_of_lexical valid
  obtain ⟨sameControl, sameStack⟩ := yieldedPlanWith_control found
  have grows : yielded.heap.size ≤ extracted.state.heap.size :=
    (ObjectiveBendDemandForcing.yieldedPlan_heapForces addr.heap found).2.2.1
  obtain ⟨plan, isYielded⟩ := resume_requires_yield response yielded (by rw [hs]; rfl)
  have s0Eq : s0 = ⟨yielded.heap, .evaluate response [], yielded.stack⟩ := by
    simp only [resume, isYielded, Option.some.injEq] at hs; subst hs; rfl
  have t0Eq : t0 = ⟨extracted.state.heap, .evaluate response [], yielded.stack⟩ := by
    simp only [resume, sameControl, isYielded, Option.some.injEq] at ht; subst ht; rw [← sameStack]
  obtain ⟨F, chain⟩ := ObjectiveBendDemandForcing.yieldedPlan_forces addr found (.evaluate response [])
    (fun _ m => by cases m)
  have s0Size : s0.heap.size = yielded.heap.size := by rw [s0Eq]
  have t0Size : t0.heap.size = extracted.state.heap.size := by rw [t0Eq]
  have heapRoom : (segmentLimits config s0).heap + (extracted.state.heap.size - yielded.heap.size) ≤
      (segmentLimits config t0).heap := by
    simp only [segmentLimits, ObjectiveBendDemandCollect.limitsPast]; omega
  have stackRoom : (segmentLimits config s0).stack ≤ (segmentLimits config t0).stack := Nat.le_refl _
  rw [← s0Eq, ← t0Eq] at chain
  obtain ⟨sy, sf, sd, sr⟩ :=
    ObjectiveBendDemandForcing.forces_segment chain heapRoom stackRoom ticks config.planBudget
  exact runSegment_transfer sy sf sd sr ran

/-- **What the kernel stores ends every segment the program's own yield ends**, alike,
under the kernel's own limits, at every lexically valid yield. The stored checkpoint is the
extraction's state settled and collected (`runSegment_checkpoint`); the extraction's state
against the yield is `forcingTransparent_of_yieldedPlan`. -/
theorem runSegment_stored_complete {config : Config} {limits : Limits}
    {budget : ObjectiveBendDemandData.Budget} {ticks : Nat} {yielded resumed : State}
    {response : Term} {extracted : ObjectiveBendDemandData.Result}
    (found : ObjectiveBendDemandData.yieldedPlan limits budget yielded = .ok extracted)
    (valid : ObjectiveBendDemandInvariant.LexicalInvariant yielded)
    (resumedExact : resume response yielded = some resumed) {segment : Segment}
    (ran : runSegment config ticks resumed = .ok segment) :
    ∃ stored segment', resume response (checkpoint extracted.state) = some stored ∧
      runSegment config ticks stored = .ok segment' ∧ Segment.Agrees segment segment' := by
  have transparent := forcingTransparent_of_yieldedPlan (config := config) valid found response ticks
  have sameControl := (yieldedPlanWith_control found).1
  obtain ⟨plan, isYielded⟩ := resume_requires_yield response yielded (by rw [resumedExact]; rfl)
  have forcedResume : resume response extracted.state =
      some {extracted.state with control := .evaluate response []} := by
    simp [resume, sameControl, isYielded]
  obtain ⟨seg1, ran1, agree1⟩ := transparent resumed _ segment resumedExact forcedResume ran
  obtain ⟨stored, seg2, storedResume, ran2, agree2⟩ := runSegment_checkpoint forcedResume ran1
  exact ⟨stored, seg2, storedResume, ran2, agree1.trans agree2⟩

/-- **What a stored checkpoint promises, of the segment that stored it.** The segment from
`start` (`ticks`, the kernel's own `segmentLimits`) yielded; `state` is exactly the
checkpoint of THAT yield's Plan extraction; and resuming `state` ends every segment resuming
that yield ends, alike, under the same config (`ForcingTransparent`, every response and tick
budget). The yield is the bounded run's own retained state, named by the run, not chosen. -/
def StoredComplete (config : Config) (ticks : Nat) (start state : State) : Prop :=
  match runBounded (segmentLimits config start) ticks start with
  | .yielded _ yielded =>
    match ObjectiveBendDemandData.yieldedPlan (segmentLimits config start) config.planBudget yielded with
    | .ok extracted =>
      state = checkpoint extracted.state ∧
        ∀ (response : Term) (ticks' : Nat), ForcingTransparent config yielded state response ticks'
    | .error _ => False
  | _ => False

/-- A segment that yielded from a start whose yield is lexically valid stored a complete
checkpoint. -/
theorem storedComplete_of_yielded {config : Config} {ticks : Nat} {start state : State} {plan : PlanAwait}
    (ran : runSegment config ticks start = .ok (.yielded state plan))
    (valid : ∀ address retained, runBounded (segmentLimits config start) ticks start = .yielded address retained →
      ObjectiveBendDemandInvariant.LexicalInvariant retained) :
    StoredComplete config ticks start state := by
  obtain ⟨address, retained, extracted, executed, extractedExact, stored⟩ := runSegment_yielded ran
  unfold StoredComplete
  rw [executed]
  simp only [extractedExact]
  refine ⟨stored, fun response ticks' s0 t0 segment hs ht ran' => ?_⟩
  obtain ⟨t1, segment', resumedStored, ran'', agree⟩ :=
    runSegment_stored_complete extractedExact (valid address retained executed) hs ran'
  rw [← stored] at resumedStored
  rw [resumedStored] at ht
  cases ht
  exact ⟨segment', ran'', agree⟩

/-- **The checkpoint a birth stores resumes as the program's own yield**, with no premise:
the yield of the program's initial state is typed (`typed_runBounded_yielded` from the
checked program), so lexically valid. -/
theorem birth_stored_complete {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : BirthRequest} (birth : Birth config snapshot height request)
    {state : State} {plan : PlanAwait} (yieldedSegment : birth.segment = .yielded state plan) :
    StoredComplete config request.envelope.sourceTicks (initial birth.program.applied.erase) state := by
  have ran := birth.segmentExact
  rw [yieldedSegment] at ran
  refine storedComplete_of_yielded ran fun _ retained executed => ?_
  obtain ⟨_, ⟨typed⟩⟩ := typed_runBounded_yielded
    (checked_initial_state birth.program.applied birth.program.checked) _ _ executed
  exact typed.lexical

/-- **The checkpoint a delivery stores resumes as the program's own yield** (the yield of
the run from the delivery's own resumed state), if the checkpoint it decoded was typed
(`delivery_checkpoint_typed`'s premise, which `Kernel.ObjectiveCheckpointInvariant.
stored_checkpoints_typed` discharges on every reachable world:
`reachable_delivery_stored_complete`). -/
theorem delivery_stored_complete {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : DeliverRequest}
    (delivery : Delivery config snapshot height request)
    (prior : ∃ types, Nonempty (StateTyping delivery.program.assumptions types delivery.state
      delivery.program.checked.type))
    {state : State} {plan : PlanAwait} (yieldedSegment : delivery.segment = .yielded state plan) :
    StoredComplete config delivery.envelope.sourceTicks delivery.resumed state := by
  have ended := delivery.endExact
  rw [yieldedSegment] at ended
  obtain ⟨ran, _⟩ := resumedSegment_yielded ended
  obtain ⟨types, ⟨typed⟩⟩ := prior
  have computation := delivery.program.typeExact
  rw [computation] at typed
  obtain ⟨address, waiting⟩ := resume_requires_yield _ _ (by rw [delivery.resumeExact]; rfl)
  obtain ⟨resumedState⟩ := typed_resume_preserved typed waiting delivery.response.typed delivery.resumeExact
  refine storedComplete_of_yielded ran fun _ retained executed => ?_
  obtain ⟨_, ⟨typedRetained⟩⟩ := typed_runBounded_yielded resumedState _ _ executed
  exact typedRetained.lexical

/-- A satisfying point of `LexicalInvariant` (the premise's pole; its refuting pole is
`not_lexicalInvariant_danglingYield`). -/
theorem lexicalInvariant_initialNat : ObjectiveBendDemandInvariant.LexicalInvariant (initial (.nat 0)) :=
  ObjectiveBendDemandInvariant.initial_lexicalInvariant (by constructor)

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
      match runSegment config ticks t0 with
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
      match runSegment config ticks t0 with
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
  maxExtractTicks := 1600000
  maxPatience := 16
  typeFuel := 16384
  maxArtifactBytes := 4194304
  tariff := ⟨Minidregg.Kernel.ObjectiveTariff.tariffVersion, 10, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩
  abandonGrace := 16
  storageRate := 1

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

/-- **Satisfying point**, by compiled evaluation: resumed with a reply, Tally's forced first
yield ends its next segment (a yield publishing 5) as its own yield does (also an instance
of `forcingTransparent_of_yieldedPlan`; kept as the executed cross-check the
`transparency` gate reads). -/
theorem forcingTransparent_tally : ForcingTransparent tallyConfig tallyYield tallyForced tallyReply 200000 :=
  forcingTransparent_of_check (by native_decide)

/-- **Refuting point**: a "forced" state that lost its continuation (the stack) is not
transparent: resumed, it finishes with the reply where the yield yields again. -/
theorem not_forcingTransparent_lostStack :
    ¬ ForcingTransparent tallyConfig tallyYield {tallyForced with stack := []} tallyReply 200000 :=
  not_forcingTransparent_of_refute (by native_decide)

/-! ### Limits counted from zero refute the claim; the kernel's limits keep it

`ObjectiveBendDemandCollect.largerYield` yields with two cells; the checkpoint of its Plan
extraction has five (`largerYield_checkpoint_grows`). Resumed with a function that allocates
two cells and returns a record, the yield finishes within a heap limit of 6 counted from zero
(2 → 4 cells) where its checkpoint runs out of heap (5 → 7 > 6): under such limits a stored
checkpoint does NOT resume as the program's own yield (`absolute_limits_refuted`). The
kernel counts a segment's limits from its own heap (`segmentLimits`): with an allocation room
of 6 both finish, alike (`largerYield_resumes_exactly`). Reverting `runSegment` to
`config.limits` turns that decided instance false. -/

def growResponse : Term := .lam (.record [("x", .nat 1)])

/-- The checkpoint stored at `largerYield` (its Plan extracted, settled, collected). -/
def largerStored : State :=
  match ObjectiveBendDemandData.yieldedPlan ObjectiveBendDemandCollect.largerLimits
      ObjectiveBendDemandCollect.largerBudget ObjectiveBendDemandCollect.largerYield with
  | .ok extracted => checkpoint extracted.state
  | .error _ => ObjectiveBendDemandCollect.largerYield

def largerConfig : Config := {tallyConfig with limits := ⟨6, 64⟩, planBudget := ⟨64, 64, 256⟩}

/-- **Limits counted from zero refute the claim** (machine level, decided in the kernel):
under heap limit 6 the yield's resumption finishes and the checkpoint's runs out of heap. -/
theorem absolute_limits_refuted :
    (match resume growResponse ObjectiveBendDemandCollect.largerYield, resume growResponse largerStored with
      | some s0, some t0 =>
        (match runBounded largerConfig.limits 64 s0 with | .finished _ _ => true | _ => false) &&
          (match runBounded largerConfig.limits 64 t0 with | .suspended .capacity _ => true | _ => false)
      | _, _ => false) = true := by
  decide +kernel

/-- **The kernel's limits keep it**: the same yield, checkpoint and response under the
kernel's `runSegment` end alike. -/
theorem largerYield_resumes_exactly :
    ForcingTransparent largerConfig ObjectiveBendDemandCollect.largerYield largerStored growResponse 64 :=
  forcingTransparent_of_check (by decide +kernel)

/-! ### The converse: the kernel commits where the lazy run is refused

The forced checkpoint holds cached what the lazy yield would compute again, so its
resumption spends fewer ticks and less extraction budget. So the converse of
`runSegment_stored_complete` is FALSE, in both resources, at a lexically valid yield, under
the deployed `runSegment`:

* `stored_commits_where_lazy_exhausts`: resumed to read the record's field `a`, the yield
  needs 15 transitions and the checkpoint 11; at 12 ticks the program's own run is
  refused `exhausted` (it commits nothing; at the turn cap a delivery would commit it as a
  fault) and the stored run finishes.
* `stored_commits_where_lazy_extraction_fails`: resumed to return the record, both runs
  finish; materializing its three fields costs 4 extraction ticks each lazily and 2 each
  from the checkpoint; with a budget of 8 the program's own result extraction fails
  (`resultExtraction`, which a delivery commits as a program FAULT, `programFault`) and the
  stored segment finishes with the record.

The difference is only in resources the cache saved: `runSegment_stored_complete` is the
statement that whenever the program's own run commits, the stored run commits alike. -/

def readResponse : Term := .lam (.get (.bound 0) "a")

def returnResponse : Term := .lam (.bound 0)

/-- The lazy run refused for running out of ticks, the stored run committed. -/
def exhaustedConverseCheck (config : Config) (yielded stored : State) (response : Term) (ticks : Nat) : Bool :=
  match resume response yielded, resume response stored with
  | some s0, some t0 =>
    match runSegment config ticks s0, runSegment config ticks t0 with
    | .error .exhausted, .ok _ => true
    | _, _ => false
  | _, _ => false

theorem exhaustedConverse_of_check {config : Config} {yielded stored : State} {response : Term} {ticks : Nat}
    (checked : exhaustedConverseCheck config yielded stored response ticks = true) :
    ∃ s0 t0 segment, resume response yielded = some s0 ∧ resume response stored = some t0 ∧
      runSegment config ticks s0 = .error .exhausted ∧ runSegment config ticks t0 = .ok segment := by
  unfold exhaustedConverseCheck at checked
  split at checked
  · rename_i s0 t0 hs ht
    split at checked
    · rename_i segment r1 r2
      exact ⟨s0, t0, segment, hs, ht, r1, r2⟩
    · cases checked
  · cases checked

/-- The lazy run's result extraction failed, the stored run finished. -/
def extractionConverseCheck (config : Config) (yielded stored : State) (response : Term) (ticks : Nat) : Bool :=
  match resume response yielded, resume response stored with
  | some s0, some t0 =>
    match runSegment config ticks s0, runSegment config ticks t0 with
    | .error (.resultExtraction _), .ok (.finished _) => true
    | _, _ => false
  | _, _ => false

theorem extractionConverse_of_check {config : Config} {yielded stored : State} {response : Term} {ticks : Nat}
    (checked : extractionConverseCheck config yielded stored response ticks = true) :
    ∃ s0 t0 reason result, resume response yielded = some s0 ∧ resume response stored = some t0 ∧
      runSegment config ticks s0 = .error (.resultExtraction reason) ∧
      runSegment config ticks t0 = .ok (.finished result) := by
  unfold extractionConverseCheck at checked
  split at checked
  · rename_i s0 t0 hs ht
    split at checked
    · rename_i reason result r1 r2
      exact ⟨s0, t0, reason, result, hs, ht, r1, r2⟩
    · cases checked
  · cases checked

/-- `largerYield` is lexically valid: the converse fails at a yield the completeness
theorem covers. -/
theorem lexicalInvariant_largerYield :
    ObjectiveBendDemandInvariant.LexicalInvariant ObjectiveBendDemandCollect.largerYield := by
  refine ⟨fun address cell found => ?_, (by decide : (1 : Nat) < 2), fun frame member => ?_⟩
  · rcases address with _ | _ | address
    · simp [ObjectiveBendDemandCollect.largerYield] at found
      subst found
      exact ⟨.record (fun field member => by
        simp at member
        rcases member with rfl | rfl | rfl <;> exact .natural _), fun _ member => by simp at member⟩
    · simp [ObjectiveBendDemandCollect.largerYield] at found
      subst found
      exact ⟨.bound (by decide), fun a member => by simp at member; subst member; decide⟩
    · simp [ObjectiveBendDemandCollect.largerYield] at found
  · simp [ObjectiveBendDemandCollect.largerYield] at member
    subst member
    exact ⟨.bound (by decide), fun a member => by simp at member; subst member; decide⟩

/-- **Converse refuted, ticks.** -/
theorem stored_commits_where_lazy_exhausts :
    ∃ s0 t0 segment, resume readResponse ObjectiveBendDemandCollect.largerYield = some s0 ∧
      resume readResponse largerStored = some t0 ∧
      runSegment largerConfig 12 s0 = .error .exhausted ∧ runSegment largerConfig 12 t0 = .ok segment :=
  exhaustedConverse_of_check (by decide +kernel)

def budgetConfig : Config := {largerConfig with planBudget := ⟨64, 8, 256⟩}

/-- **Converse refuted, extraction budget**: the program's own result extraction fails
where the stored segment finishes. -/
theorem stored_commits_where_lazy_extraction_fails :
    ∃ s0 t0 reason result, resume returnResponse ObjectiveBendDemandCollect.largerYield = some s0 ∧
      resume returnResponse largerStored = some t0 ∧
      runSegment budgetConfig 64 s0 = .error (.resultExtraction reason) ∧
      runSegment budgetConfig 64 t0 = .ok (.finished result) :=
  extractionConverse_of_check (by decide +kernel)

/-- The program's own result-extraction failure is a program FAULT a delivery commits
(the await ends `faulted`), where the stored run commits the finished result. -/
theorem lazy_extraction_failure_commits_as_fault (config : Config) (envelope : Nat) (reason : String) :
    (faultOr config envelope (.resultExtraction reason) :
      Except ObjectiveActivity.Refusal (Segment × Option YieldCommit)) =
      .ok (.faulted s!"result extraction: {reason}", none) := rfl

/-! ### The difference is resources only

The converse instances above are resource refusals of the program's own run. Every case is
one: whenever resuming the stored checkpoint commits a segment, resuming the program's own
yield commits a segment that agrees, under every resource vector above a threshold
(`runSegment_stored_converse`): heap room past the segment's start, stack, ticks, extraction
ticks, and NOT more output nodes or bytes, which stay the deployment's
(`Config.withResources`). With `runSegment_stored_complete` (the lazy commits ⇒ the stored
commits alike, under the kernel's own limits), the stored checkpoint introduces no behaviour
of its own: it changes only what the run costs.

The proof is backward simulation along the normalization (`ObjectiveBendDemandForcingBack`,
`ObjectiveBendDemandForcingConverse`): the stored checkpoint is in a `Chain` with the yield
(forcing, settling, collection), a forced run that halts has a lazy run that halts (the lazy
run does the closed demands the extraction cached, each known to finish), and the extraction
transfers back above a threshold. -/

open Minidregg.Theory.ObjectiveBendDemandForcing (Chain Ending endsWith EndsAbove LimitsLe)

/-- The deployment with another resource vector: heap room past a segment's start, stack,
and extraction ticks (segment ticks are `runSegment`'s own argument). Every other field, the
output sizes (`planBudget.nodes`, `planBudget.bytes`) among them, is the deployment's. -/
def _root_.Minidregg.Kernel.ObjectiveActivity.Config.withResources (config : Config) (heap stack extractTicks : Nat) : Config :=
  {config with limits := ⟨heap, stack⟩, planBudget := {config.planBudget with ticks := extractTicks}}

/-- The kernel segment an ending commits (its Plan decoded; the stored state is free). -/
def Segment.OfEnding : Ending → Segment → Prop
  | .yielded d, .yielded _ plan => decodePlan d = .ok plan
  | .finished d, .finished result => result = d
  | .divergent, .faulted reason => reason = "divergent"
  | .refused r, .faulted reason => reason = reprStr r
  | _, _ => False

/-- A committed segment ends with an ending. -/
theorem runSegment_ends {config : Config} {ticks : Nat} {start : State} {segment : Segment}
    (ran : runSegment config ticks start = .ok segment) :
    ∃ e y, endsWith (segmentLimits config start) ticks config.planBudget start = some (e, y) ∧
      Segment.OfEnding e segment := by
  unfold runSegment at ran
  split at ran
  · rename_i address yielded equation
    split at ran
    · rename_i extracted extractedExact
      simp only [bind, Except.bind] at ran
      split at ran
      · cases ran
      · rename_i plan decoded
        cases ran
        exact ⟨.yielded extracted.value, yielded, by simp [endsWith, equation, extractedExact], decoded⟩
    · cases ran
  · rename_i value finished equation
    split at ran
    · rename_i result resultExact
      cases ran
      exact ⟨.finished result.value, finished, by simp [endsWith, equation, resultExact], rfl⟩
    · cases ran
  · rename_i address y equation
    cases ran
    exact ⟨.divergent, y, by simp [endsWith, equation], rfl⟩
  · rename_i reason y equation
    cases ran
    exact ⟨.refused reason, y, by simp [endsWith, equation], rfl⟩
  · cases ran

/-- An ending commits a segment that agrees with every segment it commits. -/
theorem runSegment_of_ends {config : Config} {ticks : Nat} {start : State} {e : Ending} {y : State}
    (ran : endsWith (segmentLimits config start) ticks config.planBudget start = some (e, y))
    {other : Segment} (of : Segment.OfEnding e other) :
    ∃ segment, runSegment config ticks start = .ok segment ∧ Segment.Agrees segment other := by
  unfold endsWith at ran
  unfold runSegment
  split at ran
  · rename_i address yy equation
    rw [equation]
    split at ran
    · rename_i r found
      simp only [Option.some.injEq, Prod.mk.injEq] at ran
      obtain ⟨rfl, rfl⟩ := ran
      cases other with
      | yielded c plan =>
        simp only [Segment.OfEnding] at of
        exact ⟨.yielded (checkpoint r.state) plan, by simp [found, of, bind, Except.bind, pure, Except.pure], rfl, rfl, rfl⟩
      | _ => simp [Segment.OfEnding] at of
    · cases ran
  · rename_i value yy equation
    rw [equation]
    split at ran
    · rename_i r found
      simp only [Option.some.injEq, Prod.mk.injEq] at ran
      obtain ⟨rfl, rfl⟩ := ran
      cases other with
      | finished result =>
        simp only [Segment.OfEnding] at of
        exact ⟨.finished r.value, by simp [found], of.symm⟩
      | _ => simp [Segment.OfEnding] at of
    · cases ran
  · rename_i address yy equation
    rw [equation]
    simp only [Option.some.injEq, Prod.mk.injEq] at ran
    obtain ⟨rfl, rfl⟩ := ran
    cases other with
    | faulted reason => simp only [Segment.OfEnding] at of; exact ⟨_, rfl, of.symm⟩
    | _ => simp [Segment.OfEnding] at of
  · rename_i reason yy equation
    rw [equation]
    simp only [Option.some.injEq, Prod.mk.injEq] at ran
    obtain ⟨rfl, rfl⟩ := ran
    cases other with
    | faulted r => simp only [Segment.OfEnding] at of; exact ⟨_, rfl, of.symm⟩
    | _ => simp [Segment.OfEnding] at of
  · cases ran

/-- Above a threshold of an `EndsAbove`, the kernel's own segment (under `withResources`)
commits what the ending commits. -/
theorem runSegment_above {config : Config} {start : State} {e : Ending} {y : State}
    {L0 : Minidregg.Theory.ObjectiveBendDemandMachine.Limits} {T0 E0 : Nat}
    (above : ∀ (L : Minidregg.Theory.ObjectiveBendDemandMachine.Limits) (T k : Nat), LimitsLe L0 L → T0 ≤ T →
      endsWith L T ⟨config.planBudget.nodes, E0 + k, config.planBudget.bytes⟩ start = some (e, y))
    {other : Segment} (of : Segment.OfEnding e other) (heap stack ticks extract : Nat)
    (heapEnough : L0.heap ≤ heap) (stackEnough : L0.stack ≤ stack) (ticksEnough : T0 ≤ ticks)
    (extractEnough : E0 ≤ extract) :
    ∃ segment, runSegment (config.withResources heap stack extract) ticks start = .ok segment ∧
      Segment.Agrees segment other := by
  have lim : LimitsLe L0 (segmentLimits (config.withResources heap stack extract) start) := by
    refine ⟨?_, stackEnough⟩
    show L0.heap ≤ start.heap.size + heap
    omega
  have run := above _ ticks (extract - E0) lim ticksEnough
  have budgetEq : (config.withResources heap stack extract).planBudget =
      ⟨config.planBudget.nodes, E0 + (extract - E0), config.planBudget.bytes⟩ := by
    simp only [Config.withResources]
    congr 1
    omega
  rw [← budgetEq] at run
  exact runSegment_of_ends run of

/-- **The converse of `runSegment_stored_complete`: the difference is resources only.**
Whenever resuming the checkpoint the kernel stores from a lexically valid yield commits a
segment (under any config and ticks), resuming the program's OWN yield commits a segment that
agrees (the same Plan, result or fault) under every resource vector above a threshold, with
the deployment's output sizes. (It is not "the same budget, the same result":
`stored_commits_where_lazy_exhausts` and `stored_commits_where_lazy_extraction_fails` are
that refuted.) -/
theorem runSegment_stored_converse {config : Config} {limits : Minidregg.Theory.ObjectiveBendDemandMachine.Limits}
    {budget : ObjectiveBendDemandData.Budget} {ticks : Nat} {yielded resumed stored : State} {response : Term}
    {extracted : ObjectiveBendDemandData.Result}
    (found : ObjectiveBendDemandData.yieldedPlan limits budget yielded = .ok extracted)
    (valid : ObjectiveBendDemandInvariant.LexicalInvariant yielded)
    (resumedExact : resume response yielded = some resumed)
    (storedExact : resume response (checkpoint extracted.state) = some stored) {segment : Segment}
    (ran : runSegment config ticks stored = .ok segment) :
    ∃ (heap0 stack0 ticks0 extract0 : Nat), ∀ (heap stack ticks' extract : Nat), heap0 ≤ heap → stack0 ≤ stack →
      ticks0 ≤ ticks' → extract0 ≤ extract →
      ∃ segment', runSegment (config.withResources heap stack extract) ticks' resumed = .ok segment' ∧
        Segment.Agrees segment' segment := by
  have chain := ObjectiveBendDemandForcing.chain_checkpoint
    (ObjectiveBendDemandForcing.addrValid_of_lexical valid) found
  obtain ⟨t0, again, chain0⟩ := chain.resume response resumedExact
  rw [storedExact] at again
  cases again
  obtain ⟨e, y', ends, of⟩ := runSegment_ends ran
  obtain ⟨y, _, L0, T0, E0, above⟩ := chain0.back ends
  exact ⟨L0.heap, L0.stack, T0, E0, fun heap stack ticks' extract h s t x =>
    runSegment_above above of heap stack ticks' extract h s t x⟩

/-- **The continuation states, not only the Plans.** When the stored run yields and stores
`next`, the program's own run yields the same Plan Data above a threshold, and the program's
OWN yielded state is in a `Chain` with `next`, so every later response resumes the two to a
chain again (`Chain.resume`, `Chain.resume_back`) and the converse holds again at the next
segment. The premise names the stored run's own retained yield (`runSegment_yielded`): it is
lexically valid (every kernel run of a typed state is). -/
theorem runSegment_stored_next {config : Config} {limits : Minidregg.Theory.ObjectiveBendDemandMachine.Limits}
    {budget : ObjectiveBendDemandData.Budget} {ticks : Nat} {yielded resumed stored next : State} {response : Term}
    {extracted : ObjectiveBendDemandData.Result} {plan : PlanAwait}
    (found : ObjectiveBendDemandData.yieldedPlan limits budget yielded = .ok extracted)
    (valid : ObjectiveBendDemandInvariant.LexicalInvariant yielded)
    (resumedExact : resume response yielded = some resumed)
    (storedExact : resume response (checkpoint extracted.state) = some stored)
    (ran : runSegment config ticks stored = .ok (.yielded next plan))
    (validNext : ∀ address retained, runBounded (segmentLimits config stored) ticks stored = .yielded address retained →
      ObjectiveBendDemandInvariant.LexicalInvariant retained) :
    ∃ (d : ObjectiveBendDemandData.Data) (own : State), decodePlan d = .ok plan ∧
      EndsAbove resumed config.planBudget (.yielded d) own ∧ Chain own next := by
  have chain := ObjectiveBendDemandForcing.chain_checkpoint
    (ObjectiveBendDemandForcing.addrValid_of_lexical valid) found
  obtain ⟨t0, again, chain0⟩ := chain.resume response resumedExact
  rw [storedExact] at again
  cases again
  obtain ⟨address, retained, extracted', executed, extractedExact, nextExact⟩ := runSegment_yielded ran
  have ends : endsWith (segmentLimits config stored) ticks config.planBudget stored =
      some (.yielded extracted'.value, retained) := by
    simp [endsWith, executed, extractedExact]
  obtain ⟨own, above, c⟩ := chain0.next ends
    (ObjectiveBendDemandForcing.addrValid_of_lexical (validNext address retained executed)) extractedExact
  obtain ⟨e, y', ends', of⟩ := runSegment_ends ran
  rw [ends] at ends'
  simp only [Option.some.injEq, Prod.mk.injEq] at ends'
  obtain ⟨rfl, rfl⟩ := ends'
  subst nextExact
  exact ⟨extracted'.value, own, of, above, c⟩

/-- The converse's premise is inhabited, at the very point where the same budget fails
(`stored_commits_where_lazy_exhausts`): `largerYield` is lexically valid, its Plan extracts,
both resumptions exist, and the stored run commits. -/
theorem stored_converse_inhabited :
    ∃ (extracted : ObjectiveBendDemandData.Result) (resumed stored : State) (segment : Segment),
      ObjectiveBendDemandData.yieldedPlan ObjectiveBendDemandCollect.largerLimits
        ObjectiveBendDemandCollect.largerBudget ObjectiveBendDemandCollect.largerYield = .ok extracted ∧
      ObjectiveBendDemandInvariant.LexicalInvariant ObjectiveBendDemandCollect.largerYield ∧
      resume readResponse ObjectiveBendDemandCollect.largerYield = some resumed ∧
      resume readResponse (checkpoint extracted.state) = some stored ∧
      runSegment largerConfig 12 stored = .ok segment ∧
      runSegment largerConfig 12 resumed = .error .exhausted := by
  have extracts : (match ObjectiveBendDemandData.yieldedPlan ObjectiveBendDemandCollect.largerLimits
      ObjectiveBendDemandCollect.largerBudget ObjectiveBendDemandCollect.largerYield with
      | .ok _ => true | .error _ => false) = true := by decide +kernel
  cases found : ObjectiveBendDemandData.yieldedPlan ObjectiveBendDemandCollect.largerLimits
      ObjectiveBendDemandCollect.largerBudget ObjectiveBendDemandCollect.largerYield with
  | error _ => rw [found] at extracts; cases extracts
  | ok extracted =>
    have stored_def : largerStored = checkpoint extracted.state := by
      unfold largerStored; rw [found]
    obtain ⟨s0, t0, segment, hs, ht, lazy, storedRun⟩ := stored_commits_where_lazy_exhausts
    rw [stored_def] at ht
    exact ⟨extracted, s0, t0, segment, rfl, lexicalInvariant_largerYield, hs, ht, storedRun, lazy⟩

/-- **"The difference is resources only"**, as a property of a pair of resumed states: every
segment `stored` commits (under `config` and any ticks), `resumed` commits alike under every
resource vector above a threshold. `runSegment_stored_converse` is this property at every
checkpoint the kernel stores from a lexically valid yield; `not_resourcesOnly_lostStack` is a
planted fault (a "checkpoint" that lost its continuation) at which it is false. -/
def ResourcesOnly (config : Config) (resumed stored : State) : Prop :=
  ∀ (ticks : Nat) (segment : Segment), runSegment config ticks stored = .ok segment →
    ∃ (heap0 stack0 ticks0 extract0 : Nat), ∀ (heap stack ticks' extract : Nat), heap0 ≤ heap → stack0 ≤ stack →
      ticks0 ≤ ticks' → extract0 ≤ extract →
      ∃ segment', runSegment (config.withResources heap stack extract) ticks' resumed = .ok segment' ∧
        Segment.Agrees segment' segment

theorem resourcesOnly_of_yieldedPlan {config : Config} {limits : Minidregg.Theory.ObjectiveBendDemandMachine.Limits}
    {budget : ObjectiveBendDemandData.Budget} {yielded resumed stored : State} {response : Term}
    {extracted : ObjectiveBendDemandData.Result}
    (found : ObjectiveBendDemandData.yieldedPlan limits budget yielded = .ok extracted)
    (valid : ObjectiveBendDemandInvariant.LexicalInvariant yielded)
    (resumedExact : resume response yielded = some resumed)
    (storedExact : resume response (checkpoint extracted.state) = some stored) :
    ResourcesOnly config resumed stored :=
  fun _ _ ran => runSegment_stored_converse found valid resumedExact storedExact ran

/-- A segment a state commits under one resource vector, it commits above a threshold (the
state is in a chain with itself). -/
theorem runSegment_self_above {config : Config} {ticks : Nat} {start : State} {segment : Segment}
    (ran : runSegment config ticks start = .ok segment) :
    ∃ (heap0 stack0 ticks0 extract0 : Nat), ∀ (heap stack ticks' extract : Nat), heap0 ≤ heap → stack0 ≤ stack →
      ticks0 ≤ ticks' → extract0 ≤ extract →
      ∃ segment', runSegment (config.withResources heap stack extract) ticks' start = .ok segment' ∧
        Segment.Agrees segment' segment := by
  obtain ⟨e, y, ends, of⟩ := runSegment_ends ran
  obtain ⟨_, _, L0, T0, E0, above⟩ := (Chain.settles (ObjectiveBendDemandCollect.Agree.refl start)).back ends
  exact ⟨L0.heap, L0.stack, T0, E0, fun heap stack ticks' extract h s t x =>
    runSegment_above above of heap stack ticks' extract h s t x⟩

/-- Two segments that agree with segments that do not agree cannot come from one run. -/
theorem not_resourcesOnly_of_disagree {config : Config} {resumed stored : State} {ticks : Nat}
    {lazy forced : Segment} (lazyRan : runSegment config ticks resumed = .ok lazy)
    (storedRan : runSegment config ticks stored = .ok forced) (differ : ¬ Segment.Agrees lazy forced) :
    ¬ ResourcesOnly config resumed stored := by
  intro only
  obtain ⟨h1, s1, t1, x1, conv⟩ := only ticks forced storedRan
  obtain ⟨h2, s2, t2, x2, self⟩ := runSegment_self_above lazyRan
  obtain ⟨seg1, ran1, agree1⟩ := conv (h1 + h2) (s1 + s2) (t1 + t2) (x1 + x2) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨seg2, ran2, agree2⟩ := self (h1 + h2) (s1 + s2) (t1 + t2) (x1 + x2) (by omega) (by omega) (by omega) (by omega)
  rw [ran1] at ran2
  cases ran2
  exact differ (agree2.symm.trans agree1)

/-- The lazy and the lost-stack runs commit, and do not agree. -/
def lostStackCheck : Bool :=
  match resume tallyReply tallyYield, resume tallyReply {tallyForced with stack := []} with
  | some s0, some t0 =>
    match runSegment tallyConfig 200000 s0, runSegment tallyConfig 200000 t0 with
    | .ok lazy, .ok forced => !Segment.agreesB lazy forced
    | _, _ => false
  | _, _ => false

theorem lostStack_checked : lostStackCheck = true := by native_decide

/-- **Planted fault**: a "checkpoint" that lost its continuation (Tally's forced first yield
with an empty stack) is not resources-only: resumed, it finishes where the program's own yield
yields again, and no resources reconcile them. -/
theorem not_resourcesOnly_lostStack :
    ∃ s0 t0, resume tallyReply tallyYield = some s0 ∧ resume tallyReply {tallyForced with stack := []} = some t0 ∧
      ¬ ResourcesOnly tallyConfig s0 t0 := by
  have checked := lostStack_checked
  unfold lostStackCheck at checked
  split at checked
  · rename_i s0 t0 hs ht
    split at checked
    · rename_i lazy forced r1 r2
      refine ⟨s0, t0, hs, ht, not_resourcesOnly_of_disagree r1 r2 ?_⟩
      intro agree
      rw [← Segment.agreesB_iff] at agree
      simp [agree] at checked
    · cases checked
  · cases checked

/-! ### The kernel spends what the envelope declares, and the envelope is priced

C3, deployed accounting (GPT-6): the actual kernel admits and pays for exactly the resources
its run may spend. A resumed segment runs `runSegment config envelope.sourceTicks resumed`:
under `segmentLimits` (the checkpoint's cells plus the deployment's allocation, and the
deployment's stack), `envelope.sourceTicks` ticks, and the deployment's extraction budget
`planBudget` (output nodes, output bytes, extraction ticks). Every component is declared by
the envelope (`Config.covers`; `heapUncovered` and `extractUncovered` refuse by name before
any run), and the envelope's price, `Tariff.workOf`, charges each declared component at its
rate. A checkpoint that grew is paid by the delivery that resumes it (`heapCovered`); the
extraction's forcing, validator work at every delivery, is declared and paid
(`extractCovered`) rather than folded into the source ceiling. -/

open Minidregg.Compiler.ObjectiveInvocationClaim (Capacity)

/-- The resource vector a resumed segment may spend, componentwise within its declared
envelope. -/
structure SpendDeclared (config : Config) (resumed : State) (envelope : Capacity) : Prop where
  heap : (segmentLimits config resumed).heap ≤ envelope.heap
  stack : (segmentLimits config resumed).stack ≤ envelope.stack
  ticks : envelope.sourceTicks ≤ config.maxTicks
  outputNodes : config.planBudget.nodes ≤ envelope.outputNodes
  outputBytes : config.planBudget.bytes ≤ envelope.outputBytes
  extractTicks : config.planBudget.ticks ≤ envelope.extractTicks

theorem spendDeclared_of {config : Config} {resumed : State} {envelope : Capacity}
    (covered : config.covers envelope = true) (heapCovered : (segmentLimits config resumed).heap ≤ envelope.heap)
    (extractCovered : config.planBudget.ticks ≤ envelope.extractTicks) : SpendDeclared config resumed envelope := by
  simp only [Config.covers, Bool.and_eq_true, decide_eq_true_eq] at covered
  obtain ⟨⟨⟨⟨⟨⟨ticks, _⟩, stack⟩, _⟩, nodes⟩, bytes⟩, _⟩ := covered
  exact ⟨heapCovered, by simpa [segmentLimits, ObjectiveBendDemandCollect.limitsPast] using stack, ticks, nodes, bytes,
    extractCovered⟩

/-- **The price covers the spend**: every component the segment may spend, at its tariff rate,
is within the envelope's price. -/
theorem SpendDeclared.priced {config : Config} {resumed : State} {envelope : Capacity}
    (spend : SpendDeclared config resumed envelope) :
    config.tariff.heap * (segmentLimits config resumed).heap + config.tariff.stack * (segmentLimits config resumed).stack +
      config.tariff.sourceTicks * envelope.sourceTicks + config.tariff.outputNodes * config.planBudget.nodes +
      config.tariff.outputBytes * config.planBudget.bytes + config.tariff.extractTicks * config.planBudget.ticks ≤
      config.tariff.workOf envelope := by
  unfold Minidregg.Kernel.ObjectiveTariff.Tariff.workOf
  have := Nat.mul_le_mul_left config.tariff.heap spend.heap
  have := Nat.mul_le_mul_left config.tariff.stack spend.stack
  have := Nat.mul_le_mul_left config.tariff.outputNodes spend.outputNodes
  have := Nat.mul_le_mul_left config.tariff.outputBytes spend.outputBytes
  have := Nat.mul_le_mul_left config.tariff.extractTicks spend.extractTicks
  omega

/-- **A delivery spends what it declared.** -/
theorem Delivery.spend {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request) :
    SpendDeclared config delivery.resumed delivery.envelope :=
  spendDeclared_of delivery.covered delivery.heapCovered delivery.extractCovered

/-- **So does an exhaustion attempt.** -/
theorem Exhaustion.spend {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ExhaustRequest} (attempt : Exhaustion config snapshot height request) :
    SpendDeclared config attempt.resumed attempt.envelope :=
  spendDeclared_of attempt.covered attempt.heapCovered attempt.extractCovered

/-- The checkpoint's cells are paid at the delivery that resumes them: its price covers the
checkpoint's heap plus the allocation, at the heap rate. -/
theorem Delivery.heap_priced {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request) :
    config.tariff.heap * (delivery.state.heap.size + config.limits.heap) ≤ config.tariff.workOf delivery.envelope := by
  have priced := (Delivery.spend delivery).priced
  have same := (resume_keeps_heap_and_stack _ _ _ delivery.resumeExact).1
  simp only [segmentLimits, ObjectiveBendDemandCollect.limitsPast, same] at priced
  omega

/-- The delivery's extraction ticks are paid at the extraction-tick rate. -/
theorem Delivery.extraction_priced {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request) :
    config.tariff.extractTicks * config.planBudget.ticks ≤ config.tariff.workOf delivery.envelope := by
  have := (Delivery.spend delivery).priced
  omega

/-- The spend's refuting pole: an envelope declaring no extraction ticks does not cover a
deployment whose extraction budget is positive (the delivery is refused `extractUncovered`). -/
theorem not_spendDeclared_noExtract {config : Config} {resumed : State} {envelope : Capacity}
    (positive : 0 < config.planBudget.ticks) (none : envelope.extractTicks = 0) :
    ¬ SpendDeclared config resumed envelope := by
  intro spend
  have := spend.extractTicks
  omega

/-- Its satisfying pole: the Tally deployment, a resumed state with an empty heap, and the
envelope declaring exactly the deployment's ceilings. -/
theorem spendDeclared_tally :
    SpendDeclared tallyConfig (initial (.nat 0))
      ⟨0, 200000, 100000, 100000, 10000, 1048576, 100000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## A delivery advances the record

After a delivery installs, its record cell holds `first.next`, whose generation
is one more than the record it consumed (`Delivery.installed_record`,
`delivery_advances_generation`), and the id of any await that record holds is
`awaitId cell (generation + 1) …`. So a second delivery of the same record that
ended the SAME await id needs `awaitId` to collide across two generations of one
cell (`second_same_await_is_collision`); a statement assuming such a pair (the
deleted `second_delivery_refused`) has a premise only a collision inhabits. The
protection against a second resume of one await is the spent claim
(`resume_consumes_once`) together with this generation advance.

A delivery that ENDS the activity is disposal: the record cell is RETIRED
(`delivery_end_vacates`: the registry's retired image), so the installed cell
holds no record (`Delivery.installed_record_ended`), every later turn on it is
refused `recordRetired`, and no second delivery of it exists. (The image lemma
`bodyOf_image` is `ObjectiveActivity.bodyOf_image`.) -/

/-- The record a segment ends carries exactly the generation it was given. -/
theorem nextRecord_generation (base : Record) (generation : Nat)
    (segment : Segment) (yielded : Option YieldCommit) :
    (nextRecord base generation segment yielded).generation = generation := by
  cases segment <;> cases yielded <;> rfl

/-- A delivery writes the record one generation on. -/
theorem Delivery.next_generation {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : DeliverRequest}
    (delivery : Delivery config snapshot height request) :
    delivery.next.generation = delivery.record.generation + 1 := by
  rw [delivery.nextExact, nextRecord_generation]

/-- A stored (fitting) record is never empty: the codec writes its frame first. -/
theorem encodeRecord_ne_nil (record : Record) (fits : record.Fits) : encodeRecord record ≠ [] := by
  have frame : recordFrame ≠ [] := by decide +kernel
  obtain ⟨b, bs, h⟩ := List.exists_cons_of_ne_nil frame
  unfold encodeRecord
  rw [dif_pos fits, h]; simp

/-- **After a delivery that keeps the activity awaiting installs, its record cell
holds exactly the record it wrote**: the executor's accepted snapshot reads
`delivery.next` at the record cell (the record post is the intent's first write),
whatever seal it carried. -/
theorem Delivery.installed_record {rootBytes : Bytes → Digest} {config : Config}
    {snapshot next : Snapshot rootBytes} {height : Nat} {request : DeliverRequest}
    (delivery : Delivery config snapshot height request) (sealing : Seal)
    (installed : DurableDataIntent.execute .complete snapshot (delivery.intent sealing) = .accepted next)
    {await : Await} (awaiting : delivery.next.phase = .awaiting await) :
    readRecord next request.record = some delivery.next := by
  unfold readRecord
  rw [execute_accepted_install installed, DataSnapshot.install_canonicalBytes]
  simp [Delivery.intent, intentOf, delivery.postsExact, DataSnapshot.lookupPostBytes, Post.write,
    recordPost, postAt, recordImage, awaiting, bodyOf_image, record_roundTrip _ delivery.next_fits]

/-- **After a delivery that ENDS the activity installs, its record cell is
retired**: it holds the retired image and no record (disposal,
`delivery_end_vacates`); every later turn on it is refused `recordRetired`. -/
theorem Delivery.installed_record_ended {rootBytes : Bytes → Digest} {config : Config}
    {snapshot next : Snapshot rootBytes} {height : Nat} {request : DeliverRequest}
    (delivery : Delivery config snapshot height request) (sealing : Seal)
    (installed : DurableDataIntent.execute .complete snapshot (delivery.intent sealing) = .accepted next)
    (ended : ∀ await, delivery.next.phase ≠ .awaiting await) :
    isRetired (next.canonicalBytes request.record) = true ∧ readRecord next request.record = none := by
  have retired : isRetired (next.canonicalBytes request.record) = true := by
    rw [execute_accepted_install installed, DataSnapshot.install_canonicalBytes]
    simp [Delivery.intent, intentOf, delivery.postsExact, DataSnapshot.lookupPostBytes, Post.write,
      recordPost, postAt, recordImage_ended _ ended, isRetired_retiredImage]
  exact ⟨retired, readRecord_of_retired retired⟩

/-- **A second delivery of one record consumes the NEXT generation.** Any
delivery admitted from the snapshot an installed delivery produced, on the same
record cell, read exactly the record the first wrote, one generation on. (If the
first delivery ended the activity its record is retired and no second delivery
exists, `Delivery.installed_record_ended`; so the statement needs no awaiting
premise.) -/
theorem delivery_advances_generation {rootBytes : Bytes → Digest} {config : Config}
    {snapshot next : Snapshot rootBytes} {height later : Nat} {request again : DeliverRequest}
    (first : Delivery config snapshot height request) (sealing : Seal)
    (installed : DurableDataIntent.execute .complete snapshot (first.intent sealing) = .accepted next)
    (second : Delivery config next later again) (sameRecord : again.record = request.record) :
    second.record = first.next ∧ second.record.generation = first.record.generation + 1 := by
  have read := second.recordExact
  rw [sameRecord] at read
  have awaiting : ∃ await, first.next.phase = .awaiting await := by
    by_contra none
    have ended : ∀ await, first.next.phase ≠ .awaiting await := fun await h => none ⟨await, h⟩
    rw [(Delivery.installed_record_ended first sealing installed ended).2] at read
    cases read
  obtain ⟨await, awaiting⟩ := awaiting
  rw [Delivery.installed_record first sealing installed awaiting] at read
  have same : second.record = first.next := (Option.some.inj read).symm
  exact ⟨same, by rw [same, Delivery.next_generation first]⟩

/-- **A second delivery of one await is a collision.** If a second delivery of
the same record cell, admitted after the first installed, ends the same await id
as the first, `awaitId` takes one value at two consecutive generations of that
cell. -/
theorem second_same_await_is_collision {rootBytes : Bytes → Digest} {config : Config}
    {snapshot next : Snapshot rootBytes} {height later : Nat} {request again : DeliverRequest}
    (first : Delivery config snapshot height request) (sealing : Seal)
    (installed : DurableDataIntent.execute .complete snapshot (first.intent sealing) = .accepted next)
    (second : Delivery config next later again) (sameRecord : again.record = request.record)
    (sameAwait : second.await.id = first.await.id) :
    awaitId request.record (first.record.generation + 1) first.next.checkpointDigest =
      awaitId request.record first.record.generation first.record.checkpointDigest := by
  obtain ⟨same, _⟩ := delivery_advances_generation first sealing installed second sameRecord
  have secondId := second.idExact
  rw [sameAwait, first.idExact, sameRecord, same, Delivery.next_generation first] at secondId
  exact secondId.symm

/-! ### The statement is false of a malformed yield

`ForcingTransparent` cannot be discharged from a successful extraction alone (the first
statement of `runSegment_stored_complete` assumed it of every such yield; REFUTED here). The
yield below has a stack frame whose environment names address 1 in a one-cell heap
(it violates `LexicalInvariant`). Resumed with the identity, its own run allocates the
argument at address 1 and enters it from inside itself: a blackhole. The extraction
allocates address 1 first (the plan's field), so the forced run finds that field cached
and finishes. The discharge therefore needs a premise naming every address a yield
holds (`LexicalInvariant yielded`, which every reachable state has). Decided in the
kernel (`decide +kernel`), no compiled evaluation. -/

def danglingYield : State :=
  ⟨#[.suspended ⟨.record [("a", .nat 1)], []⟩], .yielded 0, [.argument (.bound 0) [1]]⟩

def danglingResponse : Term := .lam (.bound 0)

def danglingConfig : Config := {tallyConfig with limits := ⟨8, 8⟩, planBudget := ⟨8, 16, 64⟩}

theorem dangling_refuted :
    (match ObjectiveBendDemandData.yieldedPlan danglingConfig.limits danglingConfig.planBudget danglingYield with
      | .ok extracted => forcingOpaqueCheck danglingConfig danglingYield extracted.state danglingResponse 16
      | .error _ => false) = true := by
  decide +kernel

/-- **Counterexample.** The extraction succeeds and the premise fails at its state. -/
theorem not_forcingTransparent_dangling :
    ∃ extracted, ObjectiveBendDemandData.yieldedPlan danglingConfig.limits danglingConfig.planBudget
        danglingYield = .ok extracted ∧
      ¬ ForcingTransparent danglingConfig danglingYield extracted.state danglingResponse 16 := by
  have checked := dangling_refuted
  split at checked
  · rename_i extracted found
    exact ⟨extracted, found, not_forcingTransparent_of_refute checked⟩
  · cases checked

/-- The counterexample's yield is the one `LexicalInvariant` rules out: its stack names
an address past its heap. -/
theorem not_lexicalInvariant_danglingYield :
    ¬ ObjectiveBendDemandInvariant.LexicalInvariant danglingYield := by
  intro invariant
  have frame := invariant.2.2 (.argument (.bound 0) [1]) (by simp [danglingYield])
  have := frame.2 1 (by simp)
  simp [danglingYield] at this

/-- So no theorem discharges the premise from a successful extraction alone. -/
theorem forcingTransparent_not_of_extraction :
    ¬ ∀ (config : Config) (yielded : State) (extracted : ObjectiveBendDemandData.Result) (response : Term)
        (ticks : Nat), ObjectiveBendDemandData.yieldedPlan config.limits config.planBudget yielded = .ok extracted →
        ForcingTransparent config yielded extracted.state response ticks := by
  intro claim
  obtain ⟨extracted, found, refuted⟩ := not_forcingTransparent_dangling
  exact refuted (claim _ _ _ _ _ found)

#assert_axioms decodeCheckpoint_checkpointBytes
#assert_axioms typed_runBounded_yielded
#assert_axioms runSegment_yielded
#assert_axioms segmentCommit_yielded
#assert_axioms birth_checkpoint_typed
#assert_axioms delivery_checkpoint_typed
#assert_axioms Segment.Agrees.symm
#assert_axioms Segment.Agrees.trans
#assert_axioms segmentLimits_of_size
#assert_axioms runSegment_transfer
#assert_axioms runSegment_checkpoint
#assert_axioms forcingTransparent_of_yieldedPlan
#assert_axioms runSegment_stored_complete
#assert_axioms storedComplete_of_yielded
#assert_axioms birth_stored_complete
#assert_axioms delivery_stored_complete
#assert_axioms lexicalInvariant_initialNat
#assert_axioms dataBeq_sound
#assert_axioms dataBeq_refl
#assert_axioms Segment.agreesB_iff
#assert_axioms forcingTransparent_of_check
#assert_axioms not_forcingTransparent_of_refute
#assert_compiled forcingTransparent_tally
#assert_compiled not_forcingTransparent_lostStack
#assert_axioms absolute_limits_refuted
#assert_axioms largerYield_resumes_exactly
#assert_axioms exhaustedConverse_of_check
#assert_axioms extractionConverse_of_check
#assert_axioms lexicalInvariant_largerYield
#assert_axioms stored_commits_where_lazy_exhausts
#assert_axioms stored_commits_where_lazy_extraction_fails
#assert_axioms lazy_extraction_failure_commits_as_fault
#assert_axioms runSegment_ends
#assert_axioms runSegment_of_ends
#assert_axioms runSegment_above
#assert_axioms runSegment_stored_converse
#assert_axioms runSegment_stored_next
#assert_axioms stored_converse_inhabited
#assert_axioms resourcesOnly_of_yieldedPlan
#assert_axioms runSegment_self_above
#assert_axioms not_resourcesOnly_of_disagree
#assert_compiled lostStack_checked
#assert_axioms spendDeclared_of
#assert_axioms SpendDeclared.priced
#assert_axioms Delivery.spend
#assert_axioms Exhaustion.spend
#assert_axioms Delivery.heap_priced
#assert_axioms Delivery.extraction_priced
#assert_axioms not_spendDeclared_noExtract
#assert_axioms spendDeclared_tally
#assert_axioms nextRecord_generation
#assert_axioms Delivery.next_generation
#assert_axioms encodeRecord_ne_nil
#assert_axioms Delivery.installed_record
#assert_axioms Delivery.installed_record_ended
#assert_axioms delivery_advances_generation
#assert_axioms second_same_await_is_collision
#assert_axioms dangling_refuted
#assert_axioms not_forcingTransparent_dangling
#assert_axioms not_lexicalInvariant_danglingYield
#assert_axioms forcingTransparent_not_of_extraction
end Minidregg.Kernel.ObjectiveResumeContract
