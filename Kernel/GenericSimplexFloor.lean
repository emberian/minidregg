import Kernel.GenericSimplexOutputHistory
import Kernel.GenericSimplexErasure
import Mathlib.Tactic.SplitIfs

/-! The commit floor is the fold it replaced.

`State.lastCommitted` is maintained by `commitAt`; `lastCommittedView` folds over every
stored view. `FloorInvariant` says the field bounds every committed view and is attained
by one; it holds at `start` and is preserved by `step`. With unique view numbers
(`CausalInvariant.viewsUnique`) it gives `s.lastCommitted = lastCommittedView s`. -/
namespace Minidregg.Kernel.GenericSimplexFloor
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexLocal
open Minidregg.Kernel.GenericSimplexCausal
open Minidregg.Kernel.GenericSimplexOutputHistory
set_option autoImplicit false

structure FloorInvariant (s : State) : Prop where
  bound : ∀ n, (viewAt s n).committed.isSome = true → n ≤ s.lastCommitted
  attained : s.lastCommitted = 0 ∨ (viewAt s s.lastCommitted).committed.isSome = true

theorem floor_of_same (a b : State) (old : FloorInvariant a)
    (floor : b.lastCommitted = a.lastCommitted)
    (views : ∀ n, (viewAt b n).committed = (viewAt a n).committed) : FloorInvariant b := by
  constructor
  · intro n flag
    rw [floor]
    exact old.bound n (by rw [← views]; exact flag)
  · rw [floor, views]
    exact old.attained

@[simp] theorem floor_record (s : State) (self current deadline now : Nat)
    (checked : List Block) (offers : List Bytes) (outbox : List Message)
    (audit : List AuditEvent) (delivered : List Block) (tip : Block) (needsPoll failed : Bool)
    (floorEvidence : List Message) (served : List Nat) (relay : List (Nat × Message))
    (ahead : List (Nat × Nat)) :
    FloorInvariant { self := self, current := current, deadline := deadline, now := now, views := s.views, checked := checked, offers := offers, outbox := outbox, audit := audit, delivered := delivered, committedTip := tip, needsPoll := needsPoll, failed := failed, lastCommitted := s.lastCommitted, floorEvidence := floorEvidence, served := served, relay := relay, ahead := ahead } ↔ FloorInvariant s := by
  constructor <;> intro old <;> exact ⟨old.bound, old.attained⟩

theorem putView_floor (s : State) (v : View) (old : FloorInvariant s)
    (same : v.committed = (viewAt s v.number).committed) : FloorInvariant (putView s v) :=
  floor_of_same s _ old rfl (putView_committed s v same)

theorem initial_floor (self now deadline : Nat) (offers : List Bytes) (checked : List Block) :
    FloorInvariant {self := self, now := now, deadline := deadline, offers := offers, checked := checked} := by
  constructor
  · intro n flag
    simp [viewAt] at flag
  · exact Or.inl rfl

theorem register_floor (s : State) (message : Message) (old : FloorInvariant s) :
    FloorInvariant (register s message) := by
  unfold register
  dsimp only
  apply putView_floor _ _ old
  simp [viewAt_number]

theorem broadcast_floor (s : State) (view : Nat) (kind : Kind) (arg : Argument)
    (old : FloorInvariant s) : FloorInvariant (broadcast s view kind arg) :=
  floor_of_same (register s ⟨s.self, view, kind, arg⟩) _
    (register_floor s ⟨s.self, view, kind, arg⟩ old) rfl (fun _ => rfl)

theorem clear_committed (s : State) (view : Nat) (arg : Argument) (n : Nat) :
    (viewAt (clear s view arg) n).committed = (viewAt s n).committed := by
  cases arg <;> unfold clear <;> dsimp only <;> split
  · rfl
  · exact putView_committed s _ (by simp [viewAt_number]) n
  · exact putView_committed s _ (by simp [viewAt_number]) n
  · rfl

theorem clear_lastCommitted (s : State) (view : Nat) (arg : Argument) :
    (clear s view arg).lastCommitted = s.lastCommitted := by
  cases arg <;> unfold clear <;> dsimp only <;> split <;> rfl

theorem clear_floor (s : State) (view : Nat) (arg : Argument) (old : FloorInvariant s) :
    FloorInvariant (clear s view arg) :=
  floor_of_same s _ old (clear_lastCommitted s view arg) (clear_committed s view arg)

theorem sendCandidate_floor (s : State) (view : Nat) (arg : Argument) (old : FloorInvariant s) :
    FloorInvariant (sendCandidate s view arg) := by
  unfold sendCandidate
  dsimp only
  split
  · exact old
  · apply broadcast_floor
    apply putView_floor _ _ old
    simp [viewAt_number]

theorem castVote_floor (s : State) (view : Nat) (block : Block) (old : FloorInvariant s) :
    FloorInvariant (castVote s view block) := by
  unfold castVote
  dsimp only
  split
  · exact old
  · apply broadcast_floor
    apply putView_floor _ _ old
    simp [viewAt_number]

/-- What `doCommit` does to the committed fields: the floor field is untouched, every other
view is untouched, and a committed view stays committed. -/
structure CommitFrame (s d : State) (number : Nat) (block : Block) : Prop where
  floor : d.lastCommitted = s.lastCommitted
  others : ∀ n, n ≠ number → (viewAt d n).committed = (viewAt s n).committed
  kept : (viewAt s number).committed.isSome = true → (viewAt d number).committed.isSome = true
  fresh : (viewAt d number).committed = (viewAt s number).committed ∨
    (viewAt d number).committed = some block

theorem frame_of_put (s cleared next : State) (number : Nat) (block : Block)
    (floor : cleared.lastCommitted = s.lastCommitted)
    (same : ∀ n, (viewAt cleared n).committed = (viewAt s n).committed)
    (views : next.views =
      (putView cleared {viewAt cleared number with committed := some block}).views)
    (nextFloor : next.lastCommitted = cleared.lastCommitted) : CommitFrame s next number block := by
  have at_ : ∀ n, viewAt next n =
      viewAt (putView cleared {viewAt cleared number with committed := some block}) n := by
    intro n
    simp only [viewAt, views]
  have index : ({viewAt cleared number with committed := some block} : View).number = number :=
    viewAt_number cleared number
  have selected := viewAt_put_same cleared {viewAt cleared number with committed := some block}
  rw [index] at selected
  refine ⟨nextFloor.trans floor, ?_, ?_, ?_⟩
  · intro n other
    rw [at_, viewAt_put_other _ _ n (by rw [index]; exact other)]
    exact same n
  · intro _
    rw [at_, selected]
    rfl
  · right
    rw [at_, selected]

theorem doCommit_frame (s : State) (number : Nat) (block : Block) :
    CommitFrame s (doCommit s number block) number block := by
  have floor := clear_lastCommitted s number (some block)
  have same := clear_committed s number (some block)
  unfold doCommit
  dsimp only
  split_ifs <;> first
    | exact ⟨rfl, fun _ _ => rfl, id, Or.inl rfl⟩
    | exact ⟨floor, fun n _ => same n, fun flag => by rw [same]; exact flag, Or.inl (same number)⟩
    | exact frame_of_put s _ _ number block floor same rfl rfl

/-- The floor commit keeps the invariant: a commit above the floor raises the floor to it. -/
theorem commitAt_floor (s : State) (number : Nat) (block : Block) (old : FloorInvariant s) :
    FloorInvariant (commitAt s number block) := by
  obtain ⟨floor, others, kept, fresh⟩ := doCommit_frame s number block
  unfold commitAt raiseFloor
  dsimp only
  split
  next raised =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at raised
    constructor
    · intro n flag
      show n ≤ number
      have flag' : (viewAt (doCommit s number block) n).committed.isSome = true := flag
      by_cases chosen : n = number
      · omega
      · have prior := old.bound n (by rw [← others n chosen]; exact flag')
        omega
    · right
      show (viewAt (doCommit s number block) number).committed.isSome = true
      have exact : (viewAt (doCommit s number block) number).committed = some block := by
        simpa using raised.2
      rw [exact]
      rfl
  next kept' =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at kept'
    constructor
    · intro n flag
      rw [floor]
      by_cases chosen : n = number
      · subst chosen
        rcases fresh with same | exact
        · exact old.bound n (by rw [← same]; exact flag)
        · have notAbove : ¬ (doCommit s n block).lastCommitted < n :=
            fun above => kept' ⟨above, by rw [exact]; exact beq_self_eq_true _⟩
          omega
      · exact old.bound n (by rw [← others n chosen]; exact flag)
    · rw [floor]
      rcases old.attained with zero | reached
      · exact Or.inl zero
      · right
        by_cases chosen : s.lastCommitted = number
        · subst chosen
          exact kept reached
        · rw [others _ chosen]
          exact reached

macro "floor_step" : tactic => `(tactic|
  first
    | assumption
    | fail_if_no_progress simp only [floor_record]
    | with_reducible apply commitAt_floor
    | with_reducible apply sendCandidate_floor
    | with_reducible apply castVote_floor
    | with_reducible apply register_floor
    | with_reducible apply broadcast_floor
    | with_reducible apply clear_floor
    | with_reducible apply putView_floor
    | solve | simp_all [viewAt_number]
    | split)
macro "floor_chain" : tactic => `(tactic| repeat' floor_step)

theorem floor_fold {α : Type} (action : State → α → State)
    (each : ∀ state item, FloorInvariant state → FloorInvariant (action state item))
    (items : List α) (state : State) (old : FloorInvariant state) :
    FloorInvariant (items.foldl action state) := by
  induction items generalizing state with
  | nil => exact old
  | cons item rest ih => exact ih (action state item) (each state item old)

theorem valueRules_floor (c : Config) (s : State) (view : Nat) (block : Block)
    (old : FloorInvariant s) : FloorInvariant (valueRules c s view block) := by
  simp only [valueRules, Id.run, bind, pure]
  floor_chain

theorem argumentRules_floor (c : Config) (s : State) (view : Nat) (arg : Argument)
    (old : FloorInvariant s) : FloorInvariant (argumentRules c s view arg) := by
  simp only [argumentRules, Id.run, bind, pure]
  floor_chain

theorem progressView_floor (c : Config) (s : State) (view : Nat)
    (old : FloorInvariant s) : FloorInvariant (progressView c s view) := by
  simp only [progressView, Id.run, bind, pure]
  apply floor_fold
  · intro state arg prior
    exact argumentRules_floor c state view arg prior
  · apply floor_fold
    · intro state block prior
      exact valueRules_floor c state view block prior
    · exact old

theorem propose_floor (s : State) (old : FloorInvariant s) : FloorInvariant (propose s) := by
  unfold propose
  dsimp only
  floor_chain

theorem enterView_floor (c : Config) (s : State) (view : Nat)
    (old : FloorInvariant s) : FloorInvariant (enterView c s view) := by
  unfold enterView
  dsimp only
  split
  · apply propose_floor
    floor_chain
  · floor_chain

theorem floorJump_floor (c : Config) (s : State) (old : FloorInvariant s) :
    FloorInvariant (floorJump c s) := by
  unfold floorJump
  split
  · exact enterView_floor c s _ old
  · exact old

theorem progressOuter_floor (c : Config) (s : State) (old : FloorInvariant s) :
    FloorInvariant (progressOuter c s) := by
  simp only [progressOuter, Id.run, bind, pure]
  repeat' first
    | with_reducible apply enterView_floor
    | with_reducible apply propose_floor
    | floor_step

theorem pass_floor (c : Config) (s : State) (old : FloorInvariant s) :
    FloorInvariant (pass c s) := by
  unfold pass
  apply progressOuter_floor
  apply floorJump_floor
  apply floor_fold
  · intro state view prior
    exact progressView_floor c state view prior
  · exact old

theorem pump_floor (c : Config) (fuel : Nat) (s : State) (old : FloorInvariant s) :
    FloorInvariant (pump c fuel s) := by
  induction fuel generalizing s with
  | zero => simpa only [pump, floor_record] using old
  | succ fuel ih =>
    simp only [pump]
    split
    · apply pass_floor
      simpa only [floor_record] using old
    · apply ih
      apply pass_floor
      simpa only [floor_record] using old

theorem ingest_floor (c : Config) (s : State) (message : Message)
    (old : FloorInvariant s) : FloorInvariant (ingest c s message) := by
  unfold ingest serveFloor noteAhead serveViews
  dsimp only
  floor_chain

theorem step_floor (c : Config) (s : State) (input : Input) (old : FloorInvariant s) :
    FloorInvariant (step c s input) := by
  unfold step
  dsimp only
  split
  · floor_chain
  · apply pump_floor
    cases input with
    | delivery message => exact ingest_floor c s message old
    | deliveryAt now message =>
      apply ingest_floor
      floor_chain
    | checked block => dsimp only; floor_chain
    | offer payload => dsimp only; floor_chain
    | poll => exact old
    | tick now =>
      dsimp only
      repeat' first
        | with_reducible apply pump_floor
        | floor_step

theorem start_floor (c : Config) (self now : Nat) (offers : List Bytes)
    (checked : List Block) : FloorInvariant (start c self now offers checked) := by
  unfold start
  split
  · exact floor_of_same _ _ (initial_floor self now now [] []) rfl (fun _ => rfl)
  · apply pump_floor
    apply enterView_floor
    exact initial_floor self now (now + c.timeout) offers checked

/-! ## The invariant is the fold -/

private theorem committed_fold (views : List View) (acc : Nat) :
    let result := views.foldl
      (fun acc v => if v.committed.isSome then max acc v.number else acc) acc
    acc ≤ result ∧
      (∀ v ∈ views, v.committed.isSome = true → v.number ≤ result) ∧
      (result = acc ∨ ∃ v ∈ views, v.committed.isSome = true ∧ v.number = result) := by
  induction views generalizing acc with
  | nil => simp
  | cons head rest ih =>
    simp only [List.foldl_cons]
    by_cases flag : head.committed.isSome = true
    · rw [if_pos flag]
      obtain ⟨lower, upper, source⟩ := ih (max acc head.number)
      refine ⟨by omega, ?_, ?_⟩
      · intro v member committed
        rcases List.mem_cons.mp member with same | inside
        · subst same; omega
        · exact upper v inside committed
      · rcases source with same | ⟨v, inside, committed, number⟩
        · by_cases order : head.number ≤ acc
          · exact Or.inl (by omega)
          · exact Or.inr ⟨head, List.mem_cons_self, flag, by omega⟩
        · exact Or.inr ⟨v, List.mem_cons_of_mem _ inside, committed, number⟩
    · rw [if_neg flag]
      obtain ⟨lower, upper, source⟩ := ih acc
      refine ⟨lower, ?_, ?_⟩
      · intro v member committed
        rcases List.mem_cons.mp member with same | inside
        · subst same; exact absurd committed flag
        · exact upper v inside committed
      · rcases source with same | ⟨v, inside, committed, number⟩
        · exact Or.inl same
        · exact Or.inr ⟨v, List.mem_cons_of_mem _ inside, committed, number⟩

private theorem find_member (views : List View) (v : View)
    (unique : (views.map View.number).Nodup) (member : v ∈ views) :
    views.find? (fun w => w.number == v.number) = some v := by
  induction views with
  | nil => cases member
  | cons head rest ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with same | inside
    · subst same
      simp
    · have different : (head.number == v.number) = false := by
        have other : head.number ≠ v.number := fun equal =>
          unique.1 (equal ▸ List.mem_map_of_mem inside)
        simpa using other
      rw [List.find?_cons, different]
      exact ih unique.2 inside

theorem viewAt_member (s : State) (v : View) (unique : ViewsUnique s) (member : v ∈ s.views) :
    viewAt s v.number = v := by
  unfold viewAt
  rw [find_member s.views v unique member]
  rfl

theorem committed_member (s : State) (n : Nat)
    (flag : (viewAt s n).committed.isSome = true) :
    ∃ v ∈ s.views, v.committed.isSome = true ∧ v.number = n := by
  unfold viewAt at flag
  cases found : s.views.find? (fun v => v.number == n) with
  | none => simp [found] at flag
  | some v =>
    rw [found] at flag
    exact ⟨v, List.mem_of_find?_eq_some found, flag, by
      simpa using List.find?_some found⟩

/-- The maintained field equals the fold over the stored views. -/
theorem floor_eq_fold (s : State) (unique : ViewsUnique s) (floor : FloorInvariant s) :
    s.lastCommitted = lastCommittedView s := by
  obtain ⟨_, upper, source⟩ := committed_fold s.views 0
  change lastCommittedView s = 0 ∨ _ at source
  change ∀ v ∈ s.views, v.committed.isSome = true → v.number ≤ lastCommittedView s at upper
  apply Nat.le_antisymm
  · rcases floor.attained with zero | reached
    · omega
    · obtain ⟨v, member, committed, number⟩ := committed_member s _ reached
      have bound := upper v member committed
      omega
  · rcases source with zero | ⟨v, member, committed, number⟩
    · omega
    · have selected := viewAt_member s v unique member
      have bound := floor.bound v.number (by rw [selected]; exact committed)
      have reached : v.number = lastCommittedView s := number
      omega

/-- `LastCommittedSpec`, in the form that is true: on every state reached from `start` by
`step`, the commit floor is the highest locally committed view. -/
structure FloorSpec (s : State) : Prop where
  causal : CausalInvariant s
  floor : FloorInvariant s

theorem start_floorSpec (c : Config) (self now : Nat) (offers : List Bytes)
    (checked : List Block) : FloorSpec (start c self now offers checked) :=
  ⟨start_causal c self now offers checked, start_floor c self now offers checked⟩

theorem step_floorSpec (c : Config) (s : State) (input : Input) (old : FloorSpec s) :
    FloorSpec (step c s input) :=
  ⟨step_causal c s input old.causal, step_floor c s input old.floor⟩

theorem lastCommitted_spec (s : State) (spec : FloorSpec s) :
    s.lastCommitted = lastCommittedView s :=
  floor_eq_fold s spec.causal.viewsUnique spec.floor

/-- Teeth: the invariant is not vacuous. A state whose field lags its committed view fails it. -/
theorem lagging_floor_refused :
    ¬ FloorInvariant { self := 0, deadline := 0, views := [{ number := 1, committed := some [] }] } := by
  intro bad
  have bound := bad.bound 1 (by decide)
  revert bound
  decide

#assert_axioms commitAt_floor
#assert_axioms step_floor
#assert_axioms start_floor
#assert_axioms floor_eq_fold
#assert_axioms start_floorSpec
#assert_axioms step_floorSpec
#assert_axioms lastCommitted_spec
#assert_axioms lagging_floor_refused
#assert_axioms Minidregg.Kernel.GenericSimplexErasure.step_erase
#assert_axioms Minidregg.Kernel.GenericSimplexErasure.liveStep_run
#assert_axioms Minidregg.Kernel.GenericSimplexErasure.rebase_observational
end Minidregg.Kernel.GenericSimplexFloor
