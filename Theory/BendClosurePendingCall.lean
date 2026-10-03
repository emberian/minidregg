/- A pending original call has a different heap role from a retained Value.
The original application rows are structurally reifiable while the named Walk
is still deciding reducibility. Only actual Walk.need justifies promotion. -/
import Theory.BendClosureApplicationLeaf

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

inductive PendingCall (book : Book) (program : Program) (heap : Heap) : Nat → Term → Prop
  | retained {pointer : Nat} {source : Term} :
      RetainedReady book program heap pointer source → PendingCall book program heap pointer source
  | application {pointer function argument : Nat} {q : Quan} {f x : Term} :
      heap.get? pointer = some (.application q function argument) →
      PendingCall book program heap function f → RetainedReady book program heap argument x →
      PendingCall book program heap pointer (.App q f x)

theorem PendingCall.denotes {book : Book} {program : Program} {heap : Heap}
    {pointer : Nat} {source : Term} (pending : PendingCall book program heap pointer source) :
    Denotes program heap pointer source := by
  induction pending with
  | retained ready => exact ready.denotes
  | application row function argument ih => exact .application row ih argument.denotes

theorem PendingCall.extends {book : Book} {program : Program} {old next : Heap}
    {pointer : Nat} {source : Term} (extension : Extends old next)
    (pending : PendingCall book program old pointer source) : PendingCall book program next pointer source := by
  induction pending with
  | retained ready => exact .retained (ready.extends extension)
  | application row function argument ih =>
    exact .application (extension _ _ row) ih (argument.extends extension)

/-- Promotion uses actual source Value inversion at every application edge.
An arbitrary reducible resident application cannot discharge this premise. -/
theorem PendingCall.promote {book : Book} {program : Program} {heap : Heap}
    {pointer : Nat} {source : Term} (pending : PendingCall book program heap pointer source) :
    Value book source → RetainedReady book program heap pointer source := by
  induction pending with
  | retained ready => intro value; exact ready
  | application row function argument ih =>
    intro value
    exact .application row (ih (value_app value).1) argument value

theorem allocate_pending_call {book : Book} (limits : Limits) (library : Library) (state : State)
    (function argument original : Nat) (q : Quan) (heap : Heap) (f x : Term)
    (functionReady : RetainedReady book library.program state.heap function f)
    (argumentReady : RetainedReady book library.program state.heap argument x)
    (cache : CacheCertified library.program state.heap state.data)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.application q function argument) = .ok (original,heap)) :
    PendingCall book library.program heap original (.App q f x) ∧
    CacheCertified library.program heap (allocationState state heap original false).data := by
  have extension := allocate_extends allocated
  exact ⟨.application (allocate_reads_new allocated) (.retained (functionReady.extends extension))
      (argumentReady.extends extension),
    cache.allocate false allocated (by intro impossible; cases impossible)⟩

/-- A retained underapplication is produced by the real source Walk.need,
including the original definition lookup and argument Value evidence. -/
theorem underapplication_retains {book : Book} (limits : Limits) (library : Library) (state : State)
    (pc environment original : Nat) (instruction : Code) (source origin : Term)
    (values : Env) (contexts : List (Context book))
    (control : state.control = .walk pc environment original [])
    (found : library.program.code[pc]? = some instruction)
    (takes : directTakes instruction = true)
    (sourceExact : CodeDenotes library.program pc source)
    (pending : PendingCall book library.program state.heap original origin)
    (walkPrefix : WalkPrefix book origin source values [])
    (stack : RetainedStack book library.program state.heap state.stack contexts) :
    RetainedFocus book library.program (step limits library state).heap (step limits library state).control origin ∧
    RetainedStack book library.program (step limits library state).heap (step limits library state).stack contexts := by
  have value := walkPrefix.need (direct_takes_source sourceExact found takes)
  rw [step_walk_underapplication limits library state pc environment original instruction control found takes]
  exact ⟨.returned (pending.promote value) value,stack⟩

#assert_axioms PendingCall.denotes
#assert_axioms PendingCall.extends
#assert_axioms PendingCall.promote
#assert_axioms allocate_pending_call
#assert_axioms underapplication_retains
end Minidregg.Theory.BendClosureSimulation
