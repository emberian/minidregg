import Kernel.GenericSimplexFloor

/-! A committed tip has a committed view behind it.

`State.committedTip` is written only by `doCommit`, in the same breath as it marks a view
committed. `Tipped` says: the tip is empty, or some view is committed. With
`FloorInvariant` that gives the one fact the running replica's `rebase` needs from the tip:
when there is something to rebase onto, the floor view is committed (`tipped_floor`). -/
namespace Minidregg.Kernel.GenericSimplexTip
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexLocal
open Minidregg.Kernel.GenericSimplexCausal
open Minidregg.Kernel.GenericSimplexOutputHistory
open Minidregg.Kernel.GenericSimplexFloor (FloorInvariant doCommit_frame clear_committed clear_lastCommitted)
set_option autoImplicit false

def Tipped (s : State) : Prop :=
  s.committedTip = [] ∨ ∃ n, (viewAt s n).committed.isSome = true

theorem tip_of_same (a b : State) (old : Tipped a)
    (tip : b.committedTip = a.committedTip)
    (views : ∀ n, (viewAt b n).committed = (viewAt a n).committed) : Tipped b := by
  rcases old with empty | ⟨n, flag⟩
  · exact Or.inl (tip.trans empty)
  · exact Or.inr ⟨n, by rw [views]; exact flag⟩

@[simp] theorem tip_record (s : State) (self current deadline now : Nat)
    (checked : List Block) (offers : List Bytes) (outbox : List Message)
    (audit : List AuditEvent) (delivered : List Block) (needsPoll failed : Bool) (lastCommitted : Nat)
    (floorEvidence : List Message) (served : List Nat) (relay : List (Nat × Message))
    (ahead : List (Nat × Nat)) :
    Tipped { self := self, current := current, deadline := deadline, now := now, views := s.views, checked := checked, offers := offers, outbox := outbox, audit := audit, delivered := delivered, committedTip := s.committedTip, needsPoll := needsPoll, failed := failed, lastCommitted := lastCommitted, floorEvidence := floorEvidence, served := served, relay := relay, ahead := ahead } ↔ Tipped s := Iff.rfl

theorem putView_tip (s : State) (v : View) (old : Tipped s)
    (same : v.committed = (viewAt s v.number).committed) : Tipped (putView s v) :=
  tip_of_same s _ old rfl (putView_committed s v same)

theorem initial_tip (self now deadline : Nat) (offers : List Bytes) (checked : List Block) :
    Tipped {self := self, now := now, deadline := deadline, offers := offers, checked := checked} :=
  Or.inl rfl

theorem register_tip (s : State) (message : Message) (old : Tipped s) :
    Tipped (register s message) := by
  unfold register
  dsimp only
  apply putView_tip _ _ old
  simp [viewAt_number]

theorem broadcast_tip (s : State) (view : Nat) (kind : Kind) (arg : Argument)
    (old : Tipped s) : Tipped (broadcast s view kind arg) :=
  tip_of_same (register s ⟨s.self, view, kind, arg⟩) _
    (register_tip s ⟨s.self, view, kind, arg⟩ old) rfl (fun _ => rfl)

theorem clear_committedTip (s : State) (view : Nat) (arg : Argument) :
    (clear s view arg).committedTip = s.committedTip := by
  cases arg <;> unfold clear <;> dsimp only <;> split <;> rfl

theorem clear_tip (s : State) (view : Nat) (arg : Argument) (old : Tipped s) :
    Tipped (clear s view arg) :=
  tip_of_same s _ old (clear_committedTip s view arg) (clear_committed s view arg)

theorem sendCandidate_tip (s : State) (view : Nat) (arg : Argument) (old : Tipped s) :
    Tipped (sendCandidate s view arg) := by
  unfold sendCandidate
  dsimp only
  split
  · exact old
  · apply broadcast_tip
    apply putView_tip _ _ old
    simp [viewAt_number]

theorem castVote_tip (s : State) (view : Nat) (block : Block) (old : Tipped s) :
    Tipped (castVote s view block) := by
  unfold castVote
  dsimp only
  split
  · exact old
  · apply broadcast_tip
    apply putView_tip _ _ old
    simp [viewAt_number]

/-- `doCommit` leaves the tip as it was, or has the view committed. -/
theorem doCommit_committedTip (s : State) (number : Nat) (block : Block) :
    (doCommit s number block).committedTip = s.committedTip ∨
      (viewAt (doCommit s number block) number).committed.isSome = true := by
  have tipC := clear_committedTip s number (some block)
  have index : ({viewAt (clear s number (some block)) number with committed := some block} : View).number
      = number := viewAt_number _ number
  have selected := viewAt_put_same (clear s number (some block))
    {viewAt (clear s number (some block)) number with committed := some block}
  rw [index] at selected
  unfold doCommit
  dsimp only
  split_ifs <;> first
    | exact Or.inl rfl
    | exact Or.inl tipC
    | (right
       show (viewAt (putView (clear s number (some block))
         {viewAt (clear s number (some block)) number with committed := some block}) number).committed.isSome = true
       rw [selected]
       rfl)

theorem commitAt_tip (s : State) (number : Nat) (block : Block) (old : Tipped s) :
    Tipped (commitAt s number block) := by
  obtain ⟨_, others, kept, _⟩ := doCommit_frame s number block
  have committed : Tipped (doCommit s number block) := by
    rcases doCommit_committedTip s number block with same | flag
    · rcases old with empty | ⟨n, flag⟩
      · exact Or.inl (same.trans empty)
      · by_cases chosen : n = number
        · subst chosen; exact Or.inr ⟨n, kept flag⟩
        · exact Or.inr ⟨n, by rw [others n chosen]; exact flag⟩
    · exact Or.inr ⟨number, flag⟩
  unfold commitAt raiseFloor
  dsimp only
  split
  · exact tip_of_same _ _ committed rfl (fun _ => rfl)
  · exact committed


macro "tip_step" : tactic => `(tactic|
  first
    | assumption
    | fail_if_no_progress simp only [tip_record]
    | with_reducible apply commitAt_tip
    | with_reducible apply sendCandidate_tip
    | with_reducible apply castVote_tip
    | with_reducible apply register_tip
    | with_reducible apply broadcast_tip
    | with_reducible apply clear_tip
    | with_reducible apply putView_tip
    | solve | simp_all [viewAt_number]
    | split)
macro "tip_chain" : tactic => `(tactic| repeat' tip_step)

theorem tip_fold {α : Type} (action : State → α → State)
    (each : ∀ state item, Tipped state → Tipped (action state item))
    (items : List α) (state : State) (old : Tipped state) :
    Tipped (items.foldl action state) := by
  induction items generalizing state with
  | nil => exact old
  | cons item rest ih => exact ih (action state item) (each state item old)

theorem valueRules_tip (c : Config) (s : State) (view : Nat) (block : Block)
    (old : Tipped s) : Tipped (valueRules c s view block) := by
  simp only [valueRules, Id.run, bind, pure]
  tip_chain

theorem argumentRules_tip (c : Config) (s : State) (view : Nat) (arg : Argument)
    (old : Tipped s) : Tipped (argumentRules c s view arg) := by
  simp only [argumentRules, Id.run, bind, pure]
  tip_chain

theorem progressView_tip (c : Config) (s : State) (view : Nat)
    (old : Tipped s) : Tipped (progressView c s view) := by
  simp only [progressView, Id.run, bind, pure]
  apply tip_fold
  · intro state arg prior
    exact argumentRules_tip c state view arg prior
  · apply tip_fold
    · intro state block prior
      exact valueRules_tip c state view block prior
    · exact old

theorem propose_tip (s : State) (old : Tipped s) : Tipped (propose s) := by
  unfold propose
  dsimp only
  tip_chain

theorem enterView_tip (c : Config) (s : State) (view : Nat)
    (old : Tipped s) : Tipped (enterView c s view) := by
  unfold enterView
  dsimp only
  split
  · apply propose_tip
    tip_chain
  · tip_chain

theorem floorJump_tip (c : Config) (s : State) (old : Tipped s) :
    Tipped (floorJump c s) := by
  unfold floorJump
  split
  · exact enterView_tip c s _ old
  · exact old

theorem progressOuter_tip (c : Config) (s : State) (old : Tipped s) :
    Tipped (progressOuter c s) := by
  simp only [progressOuter, Id.run, bind, pure]
  repeat' first
    | with_reducible apply enterView_tip
    | with_reducible apply propose_tip
    | tip_step

theorem pass_tip (c : Config) (s : State) (old : Tipped s) :
    Tipped (pass c s) := by
  unfold pass
  apply progressOuter_tip
  apply floorJump_tip
  apply tip_fold
  · intro state view prior
    exact progressView_tip c state view prior
  · exact old

theorem pump_tip (c : Config) (fuel : Nat) (s : State) (old : Tipped s) :
    Tipped (pump c fuel s) := by
  induction fuel generalizing s with
  | zero => simpa only [pump, tip_record] using old
  | succ fuel ih =>
    simp only [pump]
    split
    · apply pass_tip
      simpa only [tip_record] using old
    · apply ih
      apply pass_tip
      simpa only [tip_record] using old

theorem ingest_tip (c : Config) (s : State) (message : Message)
    (old : Tipped s) : Tipped (ingest c s message) := by
  unfold ingest
  repeat' split
  all_goals first
    | exact old
    | (try unfold serveFloor
       try unfold noteAhead
       try unfold serveViews
       try dsimp only
       tip_chain)

theorem step_tip (c : Config) (s : State) (input : Input) (old : Tipped s) :
    Tipped (step c s input) := by
  unfold step
  dsimp only
  split
  · tip_chain
  · apply pump_tip
    cases input with
    | delivery message => exact ingest_tip c s message old
    | deliveryAt now message =>
      apply ingest_tip
      tip_chain
    | checked block => dsimp only; tip_chain
    | offer payload => dsimp only; tip_chain
    | poll => exact old
    | tick now =>
      dsimp only
      repeat' first
        | with_reducible apply pump_tip
        | tip_step

theorem start_tip (c : Config) (self now : Nat) (offers : List Bytes)
    (checked : List Block) : Tipped (start c self now offers checked) := by
  unfold start
  split
  · exact tip_of_same _ _ (initial_tip self now now [] []) rfl (fun _ => rfl)
  · apply pump_tip
    apply enterView_tip
    exact initial_tip self now (now + c.timeout) offers checked

/-- **With something to rebase onto, the floor view is committed.** -/
theorem tipped_floor {s : State} (tipped : Tipped s) (floor : FloorInvariant s)
    (nonempty : s.committedTip ≠ []) : (viewAt s s.lastCommitted).committed.isSome = true := by
  rcases tipped with empty | ⟨n, flag⟩
  · exact absurd empty nonempty
  · rcases floor.attained with zero | reached
    · have low := floor.bound n flag
      have : n = s.lastCommitted := by omega
      exact this ▸ flag
    · exact reached

#assert_axioms step_tip
#assert_axioms start_tip
#assert_axioms tipped_floor

end Minidregg.Kernel.GenericSimplexTip
