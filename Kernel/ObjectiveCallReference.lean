/- A call frame against the reference interaction tree (ObjectiveProofs).

`ObjectiveCall.exec` runs a frame as the program's OWN machine: `runCounted config.limits`
(`runCounted_outcome`: the machine's `runBounded`) on the frame's state, and at a yield whose
Plan extracts it resumes the RAW yielded state (no checkpoint, no settling, no collection) with
`returnedData result` (after a call) or `queuedData id` (after a send). So a frame's states are
the reference's own up to the identity chain, and what it commits is the reference's:

* `FrameRun`: the frame's own loop from the method's initial state, as the responses it was
  resumed with; `FrameRun.reference`: along it the frame's state is in a `Chain` with the
  reference state reached by `observe` along the same responses;
* `FrameRun.ends`: every ending the frame's run reaches is the reference node there (a yield
  `vis`, a completion `ret`, a divergence `blackhole`, a refusal `refused`);
* `exec_run_reference`, `exec_enter_reference`: a frame (or a call) that returns `result`
  ended in a completion `out` that is the reference node `ret out` of the method's initial
  state along the responses it was resumed with, each a `returnedData` or a `queuedData`, and
  `decodeReturn out` is `(result, write)`;
* `runMessage_reference`, `messageDelivery_reference`: a delivered inbox message
  (`ObjectiveSend.deliverMessage`) runs no activity machine: it runs a call tree
  (`exec`, task `enter`) as a root frame, and resumes no activity record or checkpoint. So
  the lift is the call frame's: a message that `replied result` returned the reference
  `ret out` of its method's initial state, `out` decoding to `(result, write)`.

The resources are the call path's own, NOT an activity segment's: `config.limits` counted
from zero (not `segmentLimits`), one tick count shared by the whole call tree. The reference
needs no resources beyond the output sizes, and every statement here holds under ANY limits
and ticks, so the difference changes only which frames return, never what they return. -/
import Kernel.ObjectiveSend
import Kernel.ObjectiveResumeContract

namespace Minidregg.Kernel.ObjectiveCallReference
open Minidregg.Theory Minidregg.Compiler
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ObjectiveActivityWire
open Minidregg.Kernel.ObjectiveActivity
open Minidregg.Kernel.ObjectiveCall
open Minidregg.Theory.ObjectiveBendDemandMachine (State Limits initial runBounded resume)
open Minidregg.Theory.ObjectiveBendDemandData (Data Budget)
open Minidregg.Theory.ObjectiveBendDemandForcing (Chain Ending endsWith)
open Minidregg.Theory.ObjectiveBendInteraction (Node node ending observe node_of_chain node_of_above ending_of_above)
open Minidregg.Theory.ObjectiveBendOpenRecursion (Term)
set_option autoImplicit false

/-- **A frame's own loop** from `start`: it ran to a yield whose Plan extracts (under the
frame's limits and budget, with any tick count) and resumed that raw yielded state with a
response. -/
inductive FrameRun (limits : Limits) (budget : Budget) (start : State) : List Term → State → Prop
  | start : FrameRun limits budget start [] start
  | resumed {responses : List Term} {t : State} {ticks : Nat} {address : Nat} {yielded : State} {left : Nat}
      {extracted : ObjectiveBendDemandData.Result} {response : Term} {next : State} :
      FrameRun limits budget start responses t →
      runCounted limits ticks t = (.yielded address yielded, left) →
      ObjectiveBendDemandData.yieldedPlan limits budget yielded = .ok extracted →
      resume response yielded = some next →
      FrameRun limits budget start (responses ++ [response]) next

/-- **A frame stays the reference.** Along a frame's own loop, its state is in a chain with
the reference state reached along the same responses. -/
theorem FrameRun.reference {limits : Limits} {budget : Budget} {start : State} {responses : List Term} {t : State}
    (run : FrameRun limits budget start responses t) :
    ∃ s, Chain s t ∧ ∀ rest, observe budget start (responses ++ rest) = observe budget s rest := by
  induction run with
  | start => exact ⟨start, .settles (ObjectiveBendDemandCollect.Agree.refl _), fun rest => by simp⟩
  | @resumed responses t ticks address yielded left extracted response next _ counted found resumed ih =>
    obtain ⟨s, chain, path⟩ := ih
    have bounded : runBounded limits ticks t = .yielded address yielded := by
      rw [← runCounted_outcome, counted]
    have ends : endsWith limits ticks budget t = some (.yielded extracted.value, yielded) := by
      simp [endsWith, bounded, found]
    obtain ⟨y0, chainY, above⟩ := chain.back ends
    obtain ⟨s1, resumed0, chain1⟩ := chainY.resume_back response resumed
    refine ⟨s1, chain1, fun rest => ?_⟩
    rw [List.append_assoc, List.singleton_append, path]
    simp [observe, ending_of_above above, resumed0]

/-- **What a frame's run ends with is the reference node**, under any limits and ticks. -/
theorem FrameRun.ends {limits : Limits} {budget : Budget} {start : State} {responses : List Term} {t : State}
    (run : FrameRun limits budget start responses t) {L : Limits} {T : Nat} {e : Ending} {y : State}
    (ran : endsWith L T budget t = some (e, y)) : observe budget start responses = Node.ofEnding e := by
  obtain ⟨s, chain, path⟩ := run.reference
  have := path []
  rw [List.append_nil] at this
  rw [this]
  exact (node_of_chain chain ran).1

/-- **A frame's committed yield is the reference's visible event**: the Plan it extracts
is the reference node `vis` along the responses so far. -/
theorem FrameRun.vis {limits : Limits} {budget : Budget} {start : State} {responses : List Term} {t : State}
    (run : FrameRun limits budget start responses t) {ticks address left : Nat} {yielded : State}
    {extracted : ObjectiveBendDemandData.Result}
    (counted : runCounted limits ticks t = (.yielded address yielded, left))
    (found : ObjectiveBendDemandData.yieldedPlan limits budget yielded = .ok extracted) :
    observe budget start responses = .vis extracted.value := by
  have bounded : runBounded limits ticks t = .yielded address yielded := by rw [← runCounted_outcome, counted]
  exact run.ends (L := limits) (T := ticks) (e := .yielded extracted.value) (y := yielded)
    (by simp [endsWith, bounded, found])

/-- The responses a frame is resumed with. -/
def FrameResponse (response : Term) : Prop :=
  (∃ result, response = (returnedData result).term) ∨ ∃ id, response = (queuedData id).term

/-- **A frame that returns is the reference's return.** If `exec` runs the frame at a state
of its own loop from `start` and returns `result`, the frame's run completed with `out`,
which is the reference node `ret out` along the responses so far and the further responses
it was resumed with (each a `returnedData` or a `queuedData`), and `out` decodes to
`(result, write)`. -/
theorem exec_run_reference {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {authority : Authority} {turn : TransactionId} {ctx : Ctx} {rest : List Ctx} {start : State} :
    ∀ (fuel : Nat) {responses : List Term} {t : State} {journal : Journal} {ticks : Nat} {result : Data}
      {journal' : Journal} {left : Nat},
      FrameRun config.limits config.planBudget start responses t →
      exec config snapshot height authority turn fuel (ctx :: rest) (.run t) journal ticks = .ok (result, journal', left) →
      ∃ more out write, (∀ r ∈ more, FrameResponse r) ∧
        observe config.planBudget start (responses ++ more) = .ret out ∧
        decodeReturn ctx.object.value ctx.method out = .ok (result, write) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ ran; simp [exec] at ran
  | succ fuel ih =>
    intro responses t journal ticks result journal' left run ran
    unfold exec at ran
    split at ran
    · rename_i address yielded left1 counted
      split at ran
      · cases ran
      · rename_i extracted found
        split at ran
        · cases ran
        · rename_i call decoded
          split at ran
          · cases ran
          · rename_i result1 journal1 left2 _
            split at ran
            · cases ran
            · split at ran
              · cases ran
              · rename_i next resumed
                obtain ⟨more, out, write, each, observed, decodedOut⟩ :=
                  ih (FrameRun.resumed run counted found resumed) ran
                refine ⟨(returnedData result1).term :: more, out, write, ?_, ?_, decodedOut⟩
                · intro r mem
                  rcases List.mem_cons.mp mem with here | there
                  · exact .inl ⟨result1, here⟩
                  · exact each r there
                · rw [← observed, List.append_assoc, List.singleton_append]
        · rename_i send decoded
          dsimp only at ran
          split at ran
          · cases ran
          · split at ran
            · cases ran
            · rename_i next resumed
              obtain ⟨more, out, write, each, observed, decodedOut⟩ :=
                ih (FrameRun.resumed run counted found resumed) ran
              refine ⟨(queuedData (Inbox.sendId turn journal.outbox.length)).term :: more, out, write, ?_, ?_,
                decodedOut⟩
              · intro r mem
                rcases List.mem_cons.mp mem with here | there
                · exact .inr ⟨_, here⟩
                · exact each r there
              · rw [← observed, List.append_assoc, List.singleton_append]
    · rename_i value finished left1 counted
      split at ran
      · cases ran
      · rename_i out completed
        split at ran
        · cases ran
        · rename_i result0 write decodedOut
          split at ran
          · cases ran
          · rename_i journal2 _
            simp only [Except.ok.injEq, Prod.mk.injEq] at ran
            obtain ⟨rfl, _, _⟩ := ran
            have bounded : runBounded config.limits ticks t = .finished value finished := by
              rw [← runCounted_outcome, counted]
            refine ⟨[], out.value, write, by simp, ?_, decodedOut⟩
            rw [List.append_nil]
            exact run.ends (L := config.limits) (T := ticks) (e := .finished out.value) (y := finished)
              (by simp [endsWith, bounded, completed])
    · cases ran
    · cases ran
    · cases ran

/-- **A call that returns is the reference's return of the method's initial state**: the
method its target's pinned package lowers (`loadMethod`), applied to the callee's view and
the arguments, has a reference tree that returns `out` along the responses its frame was
resumed with, and `out` decodes to `(result, write)`. -/
theorem exec_enter_reference {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {authority : Authority} {turn : TransactionId} {fuel : Nat} {stack : List Ctx} {call : CallPlan}
    {journal : Journal} {ticks : Nat} {result : Data} {journal' : Journal} {left : Nat}
    (ran : exec config snapshot height authority turn (fuel + 1) stack (.enter call) journal ticks =
      .ok (result, journal', left)) :
    ∃ (pin : Digest) (view : ObjectState) (program : Method config pin call.method (viewData view) call.args),
      loadMethod config call.target.value (packageBytes config snapshot pin) pin call.method (viewData view) call.args =
        .ok program ∧
      ∃ more out write, (∀ r ∈ more, FrameResponse r) ∧
        observe config.planBudget (initial program.applied.erase) more = .ret out ∧
        decodeReturn call.target.value call.method out = .ok (result, write) := by
  unfold exec at ran
  split at ran
  · cases ran
  · split at ran
    · cases ran
    · split at ran
      · cases ran
      · rename_i entry journal1 _
        split at ran
        · cases ran
        · cases ran
        · rename_i view _ _
          have key : ∀ (program : Method config entry.record.activePin call.method (viewData view) call.args)
              {ctx : Ctx} {rest : List Ctx} {journal : Journal}, ctx.object = call.target → ctx.method = call.method →
              exec config snapshot height authority turn fuel (ctx :: rest) (.run (initial program.applied.erase))
                journal ticks = .ok (result, journal', left) →
              ∃ more out write, (∀ r ∈ more, FrameResponse r) ∧
                observe config.planBudget (initial program.applied.erase) more = .ret out ∧
                decodeReturn call.target.value call.method out = .ok (result, write) := by
            intro program ctx rest journal object method run
            obtain ⟨more, out, write, each, observed, decoded⟩ := exec_run_reference fuel FrameRun.start run
            rw [object, method] at decoded
            exact ⟨more, out, write, each, by simpa using observed, decoded⟩
          cases loaded : loadMethod config call.target.value (packageBytes config snapshot entry.record.activePin)
              entry.record.activePin call.method (viewData view) call.args with
          | error reason =>
            simp only [loaded] at ran
            split at ran <;> (try dsimp only at ran) <;> (try split at ran) <;> simp at ran
          | ok program =>
            refine ⟨entry.record.activePin, view, program, loaded, ?_⟩
            simp only [loaded] at ran
            split at ran <;> (try dsimp only at ran) <;> (try split at ran) <;> (try dsimp only at ran) <;>
              first
              | (simp at ran; done)
              | exact key program rfl rfl ran

/-- **A delivered message that replied is the reference's return of its method.** -/
theorem runMessage_reference {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height target : Nat} {message : Inbox.Message} {result : Data} {journal : Journal}
    (ran : ObjectiveSend.runMessage config snapshot height target message = .replied result journal) :
    ∃ (args : Data) (pin : Digest) (view : ObjectState) (program : Method config pin message.method (viewData view) args),
      decodeDataBytes message.args = some args ∧
      loadMethod config target (packageBytes config snapshot pin) pin message.method (viewData view) args = .ok program ∧
      ∃ more out write, (∀ r ∈ more, FrameResponse r) ∧
        observe config.planBudget (initial program.applied.erase) more = .ret out ∧
        decodeReturn target message.method out = .ok (result, write) := by
  unfold ObjectiveSend.runMessage at ran
  split at ran
  · cases ran
  · rename_i args decoded
    split at ran
    · cases ran
    · rename_i result1 journal1 left1 executed
      split at ran
      · simp only [ObjectiveSend.Outcome.replied.injEq] at ran
        obtain ⟨rfl, _⟩ := ran
        cases fuel : ObjectiveCall.callFuel message.envelope with
        | zero => rw [fuel] at executed; simp [exec] at executed
        | succ n =>
          rw [fuel] at executed
          obtain ⟨pin, view, program, loaded, rest⟩ := exec_enter_reference executed
          exact ⟨args, pin, view, program, decoded, loaded, rest⟩
      · cases ran

/-- **(f) A message delivery's reply is the reference's**: when the delivery decided
`reply`, the call tree it ran returned the reference node of its method's initial state. -/
theorem messageDelivery_reference {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ObjectiveSend.MessageRequest}
    (delivery : ObjectiveSend.MessageDelivery config snapshot height request) {result : Data} {journal : Journal}
    (replied : delivery.outcome = .replied result journal) :
    ∃ (args : Data) (pin : Digest) (view : ObjectState)
      (program : Method config pin delivery.message.method (viewData view) args),
      decodeDataBytes delivery.message.args = some args ∧
      loadMethod config request.target (packageBytes config snapshot pin) pin delivery.message.method (viewData view)
        args = .ok program ∧
      ∃ more out write, (∀ r ∈ more, FrameResponse r) ∧
        observe config.planBudget (initial program.applied.erase) more = .ret out ∧
        decodeReturn request.target delivery.message.method out = .ok (result, write) :=
  runMessage_reference (delivery.outcomeExact.trans replied)

#assert_axioms FrameRun.reference
#assert_axioms FrameRun.ends
#assert_axioms FrameRun.vis
#assert_axioms exec_run_reference
#assert_axioms exec_enter_reference
#assert_axioms runMessage_reference
#assert_axioms messageDelivery_reference

end Minidregg.Kernel.ObjectiveCallReference
