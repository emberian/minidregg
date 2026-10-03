/- Recursive readiness of retained terms. A closure can be a Q0 thunk;
its captured environment remains ready when that thunk is later opened.
Application rows used only as reducible call spines are not required to
satisfy this relation until retained as values. -/
import Theory.BendClosureReadiness

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

mutual
inductive RetainedReady (book : Book) (program : Program) (heap : Heap) : Nat → Term → Prop
  | closure {pointer pc environment : Nat} {source : Term} {values : Env} :
      heap.get? pointer = some (.closure pc environment) →
      CodeDenotes program pc source → CapturedReady book program heap environment values →
      RetainedReady book program heap pointer (Term.sub (Env.sub values) source)
  | pair {pointer first second : Nat} {q : Quan} {a b : Term} :
      heap.get? pointer = some (.pair q first second) →
      RetainedReady book program heap first a → RetainedReady book program heap second b →
      Value book (.Tup q a b) → RetainedReady book program heap pointer (.Tup q a b)
  | application {pointer function argument : Nat} {q : Quan} {f x : Term} :
      heap.get? pointer = some (.application q function argument) →
      RetainedReady book program heap function f → RetainedReady book program heap argument x →
      Value book (.App q f x) → RetainedReady book program heap pointer (.App q f x)

inductive CapturedReady (book : Book) (program : Program) (heap : Heap) : Nat → Env → Prop
  | nil {pointer : Nat} : heap.get? pointer = some .nil →
      CapturedReady book program heap pointer []
  | cons {pointer head tail : Nat} {source : Term} {values : Env} :
      heap.get? pointer = some (.environment head tail) →
      RetainedReady book program heap head source → CapturedReady book program heap tail values →
      CapturedReady book program heap pointer (source :: values)
end

theorem RetainedReady.denotes {book : Book} {program : Program} {heap : Heap}
    {pointer : Nat} {source : Term} (ready : RetainedReady book program heap pointer source) :
    Denotes program heap pointer source := by
  apply @RetainedReady.rec book program heap
    (fun pointer source _ => Denotes program heap pointer source)
    (fun pointer values _ => EnvironmentDenotes program heap pointer values)
    ?_ ?_ ?_ ?_ ?_ pointer source ready
  · intros; exact Denotes.closure (by assumption) (by assumption) (by assumption)
  · intros; exact Denotes.pair (by assumption) (by assumption) (by assumption)
  · intros; exact Denotes.application (by assumption) (by assumption) (by assumption)
  · intros; exact EnvironmentDenotes.nil (by assumption)
  · intros; exact EnvironmentDenotes.cons (by assumption) (by assumption) (by assumption)

theorem CapturedReady.denotes {book : Book} {program : Program} {heap : Heap}
    {pointer : Nat} {values : Env} (ready : CapturedReady book program heap pointer values) :
    EnvironmentDenotes program heap pointer values := by
  apply @CapturedReady.rec book program heap
    (fun pointer source _ => Denotes program heap pointer source)
    (fun pointer values _ => EnvironmentDenotes program heap pointer values)
    ?_ ?_ ?_ ?_ ?_ pointer values ready
  · intros; exact Denotes.closure (by assumption) (by assumption) (by assumption)
  · intros; exact Denotes.pair (by assumption) (by assumption) (by assumption)
  · intros; exact Denotes.application (by assumption) (by assumption) (by assumption)
  · intros; exact EnvironmentDenotes.nil (by assumption)
  · intros; exact EnvironmentDenotes.cons (by assumption) (by assumption) (by assumption)


theorem RetainedReady.ready {book : Book} {program : Program} {heap : Heap}
    {pointer : Nat} {source : Term} (ready : RetainedReady book program heap pointer source) :
    ReadyPointer book program heap pointer source := by
  refine ⟨ready.denotes, ?_⟩
  cases ready with
  | closure row code captured => exact .inl ⟨_, _, row⟩
  | pair row first second value => exact .inr value
  | application row function argument value => exact .inr value

theorem CapturedReady.ready {book : Book} {program : Program} {heap : Heap}
    {pointer : Nat} {values : Env} (ready : CapturedReady book program heap pointer values) :
    ReadyEnvironment book program heap pointer values := by
  cases ready with
  | nil row => exact .nil row
  | cons row head tail => exact .cons row head.ready tail.ready

#assert_axioms RetainedReady.denotes
#assert_axioms CapturedReady.denotes
#assert_axioms RetainedReady.ready
#assert_axioms CapturedReady.ready
end Minidregg.Theory.BendClosureSimulation
