import Kernel.GenericSimplexAuditProjection
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.FailIfNoProgress

namespace Minidregg.Kernel.GenericSimplexStructure
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexLocal
open Minidregg.Kernel.GenericSimplexAuditProjection
set_option autoImplicit false

/-- Structural preservation only: exact actor, append-only audit and audit
ownership. This does not claim any vote guard, quorum cause or consensus fact. -/
def Preserves (before after : State) : Prop :=
  AuditExtension before after ∧ (OwnedAudit before → OwnedAudit after)

theorem preserves_refl (s : State) : Preserves s s := ⟨AuditExtension.refl s, id⟩
theorem preserves_trans {a b c : State} (ab : Preserves a b) (bc : Preserves b c) :
    Preserves a c := ⟨ab.1.trans bc.1, fun owned => bc.2 (ab.2 owned)⟩

@[simp] theorem preserves_put (a b : State) (v : View) :
    Preserves a (putView b v) ↔ Preserves a b := Iff.rfl

/-- Unrelated state fields cannot alter structural audit preservation. -/
@[simp] theorem preserves_record (a b : State) (current deadline now : Nat)
    (views : List View) (checked : List Block) (offers : List Bytes)
    (outbox : List Message) (delivered : List Block) (tip : Block)
    (needsPoll failed : Bool) :
    Preserves a { self := b.self, current := current, deadline := deadline, now := now,
      views := views, checked := checked, offers := offers, outbox := outbox,
      audit := b.audit, delivered := delivered, committedTip := tip,
      needsPoll := needsPoll, failed := failed } ↔ Preserves a b := Iff.rfl

theorem preserves_broadcast {a b : State} (view : Nat) (kind : Kind) (arg : Argument)
    (prior : Preserves a b) : Preserves a (broadcast b view kind arg) :=
  preserves_trans prior ⟨⟨broadcast_self b view kind arg, broadcast_audit_prefix b view kind arg⟩,
    broadcast_owned b view kind arg⟩
theorem preserves_clear {a b : State} (view : Nat) (arg : Argument)
    (prior : Preserves a b) : Preserves a (clear b view arg) :=
  preserves_trans prior ⟨⟨clear_self b view arg, clear_audit_prefix b view arg⟩,
    clear_owned b view arg⟩
theorem preserves_commit {a b : State} (view : Nat) (block : Block)
    (prior : Preserves a b) : Preserves a (doCommit b view block) :=
  preserves_trans prior ⟨⟨doCommit_self b view block, doCommit_audit_prefix b view block⟩,
    doCommit_owned b view block⟩
theorem preserves_candidate {a b : State} (view : Nat) (arg : Argument)
    (prior : Preserves a b) : Preserves a (sendCandidate b view arg) :=
  preserves_trans prior ⟨⟨sendCandidate_self b view arg, sendCandidate_audit_prefix b view arg⟩,
    sendCandidate_owned b view arg⟩
theorem preserves_vote {a b : State} (view : Nat) (block : Block)
    (prior : Preserves a b) : Preserves a (castVote b view block) :=
  preserves_trans prior ⟨⟨castVote_self b view block, castVote_audit_prefix b view block⟩,
    castVote_owned b view block⟩

theorem preserves_fold {α : Type} (action : State → α → State)
    (each : ∀ state item, Preserves state (action state item))
    (items : List α) {origin state : State} (prior : Preserves origin state) :
    Preserves origin (items.foldl action state) := by
  induction items generalizing state with
  | nil => exact prior
  | cons item rest ih => exact ih (preserves_trans prior (each state item))

macro "audit_step" : tactic => `(tactic|
  first
    | exact preserves_refl _
    | assumption
    | apply preserves_broadcast
    | apply preserves_clear
    | apply preserves_commit
    | apply preserves_candidate
    | apply preserves_vote
    | fail_if_no_progress simp only [preserves_put, preserves_record]
    | split)

macro "audit_chain" : tactic => `(tactic| repeat' audit_step)

theorem valueRules_preserves (c : Config) (s : State) (number : Nat) (block : Block) :
    Preserves s (valueRules c s number block) := by
  simp only [valueRules, Id.run, bind, pure]
  audit_chain

theorem argumentRules_preserves (c : Config) (s : State) (number : Nat) (arg : Argument) :
    Preserves s (argumentRules c s number arg) := by
  simp only [argumentRules, Id.run, bind, pure]
  audit_chain

theorem progressView_preserves (c : Config) (s : State) (number : Nat) :
    Preserves s (progressView c s number) := by
  simp only [progressView, Id.run, bind, pure]
  apply preserves_fold
  · intro state item; exact argumentRules_preserves c state number item
  · apply preserves_fold
    · intro state item; exact valueRules_preserves c state number item
    · exact preserves_refl s

theorem propose_preserves (s : State) : Preserves s (propose s) := by
  unfold propose
  dsimp only
  audit_chain

theorem enterView_preserves (c : Config) (s : State) (number : Nat) :
    Preserves s (enterView c s number) := by
  unfold enterView
  dsimp only
  split
  · apply preserves_trans _ (propose_preserves _)
    audit_chain
  · audit_chain

theorem progressOuter_preserves (c : Config) (s : State) :
    Preserves s (progressOuter c s) := by
  simp only [progressOuter, Id.run, bind, pure]
  repeat' first
    | apply preserves_trans _ (enterView_preserves c _ _)
    | audit_step
    | split

theorem pass_preserves (c : Config) (s : State) : Preserves s (pass c s) := by
  unfold pass
  apply preserves_trans _ (progressOuter_preserves c _)
  apply preserves_fold
  · intro state number; exact progressView_preserves c state number
  · exact preserves_refl s

theorem pump_preserves (c : Config) (fuel : Nat) (s : State) :
    Preserves s (pump c fuel s) := by
  induction fuel generalizing s with
  | zero => simp only [pump, preserves_record]; exact preserves_refl s
  | succ fuel ih =>
    simp only [pump]
    split
    · apply preserves_trans _ (pass_preserves c _)
      audit_chain
    · apply preserves_trans _ (ih _)
      apply preserves_trans _ (pass_preserves c _)
      audit_chain

theorem ingest_preserves (c : Config) (s : State) (m : Message) :
    Preserves s (ingest c s m) := by
  unfold ingest
  dsimp only
  repeat' first
    | audit_step
    | change Preserves s (putView s _)
    | split

theorem step_preserves (c : Config) (s : State) (input : Input) :
    Preserves s (step c s input) := by
  unfold step
  dsimp only
  split
  · audit_chain
  · apply preserves_trans _ (pump_preserves c c.pumpBudget _)
    cases input with
    | delivery message => exact ingest_preserves c s message
    | deliveryAt time message =>
      apply preserves_trans _ (ingest_preserves c _ message)
      audit_chain
    | checked block =>
      dsimp only
      audit_chain
    | offer payload => audit_chain
    | poll => exact preserves_refl s
    | tick time =>
      dsimp only
      repeat' first
        | apply preserves_trans _ (pump_preserves c c.pumpBudget s)
        | audit_step
        | split

theorem start_structure (c : Config) (party time : Nat) :
    (start c party time).self = party ∧ OwnedAudit (start c party time) := by
  unfold start
  dsimp only
  split
  · exact ⟨rfl, by intro event inside; cases inside⟩
  · have entered := enterView_preserves c
      {self := party, now := time, deadline := time + c.timeout} 1
    have advanced := preserves_trans entered (pump_preserves c c.pumpBudget _)
    exact ⟨advanced.1.sameSelf, advanced.2 (by intro event inside; cases inside)⟩

def structuralAuditLaws (c : Config) : StructuralAuditLaws c where
  startSelf party time := (start_structure c party time).1
  startOwned party time := (start_structure c party time).2
  stepExtension state input := (step_preserves c state input).1
  stepOwned state input := (step_preserves c state input).2

#assert_axioms valueRules_preserves
#assert_axioms progressOuter_preserves
#assert_axioms pump_preserves
#assert_axioms step_preserves
#assert_axioms start_structure
#assert_axioms structuralAuditLaws
end Minidregg.Kernel.GenericSimplexStructure
