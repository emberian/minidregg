import Kernel.GenericSimplexCausal
import Kernel.GenericSimplexReceiveProvenance
import Mathlib.Tactic.FailIfNoProgress

namespace Minidregg.Kernel.GenericSimplexReceiveScope
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexLocal
open Minidregg.Kernel.GenericSimplexCausal
open Minidregg.Kernel.GenericSimplexReceiveProvenance
set_option autoImplicit false

/-- Exact executable storage metadata needed to interpret a tally: received
senders are enrolled and each message is stored in its own numbered view. -/
def Scoped (c : Config) (state : State) : Prop :=
  state.self < c.parties ∧ ∀ view ∈ state.views, ∀ message ∈ view.received,
    message.sender < c.parties ∧ message.view = view.number

theorem viewAt_scoped {c : Config} {state : State} (scopeOK : Scoped c state) (number : Nat) :
    ∀ message ∈ (viewAt state number).received,
      message.sender < c.parties ∧ message.view = number := by
  intro message received
  have atNumber := viewAt_number state number
  unfold viewAt at received atNumber
  cases found : state.views.find? (fun v => v.number == number) with
  | none => simp [found] at received
  | some view =>
    simp only [found, Option.getD_some] at received atNumber
    have data := scopeOK.2 view (List.mem_of_find?_eq_some found) message received
    exact ⟨data.1, data.2.trans atNumber⟩

theorem putView_scoped {c : Config} {state : State} (view : View)
    (scopeOK : Scoped c state)
    (fresh : ∀ message ∈ view.received,
      message.sender < c.parties ∧ message.view = view.number) :
    Scoped c (putView state view) := by
  refine ⟨scopeOK.1, ?_⟩
  intro other member message received
  unfold putView at member
  split at member
  · obtain ⟨old, inside, same⟩ := List.mem_map.mp member
    split at same
    · subst other; exact fresh message received
    · subst other; exact scopeOK.2 old inside message received
  · rcases List.mem_append.mp member with old | added
    · exact scopeOK.2 other old message received
    · have same : other = view := by simpa using added
      subst other; exact fresh message received

theorem putView_copied_received {c : Config} {state : State} (view : View) (number : Nat)
    (scopeOK : Scoped c state)
    (sameNumber : view.number = (viewAt state number).number)
    (sameReceived : view.received = (viewAt state number).received) :
    Scoped c (putView state view) := by
  apply putView_scoped view scopeOK
  intro message received
  have data := viewAt_scoped scopeOK number message (sameReceived ▸ received)
  exact ⟨data.1, data.2.trans ((sameNumber.trans (viewAt_number state number)).symm)⟩

theorem register_scoped {c : Config} {state : State} (message : Message)
    (scopeOK : Scoped c state) (enrolled : message.sender < c.parties) :
    Scoped c (register state message) := by
  unfold register
  apply putView_scoped _ scopeOK
  intro other member
  rcases addUnique_mem _ message other member with old | same
  · have data := viewAt_scoped scopeOK message.view other old
    simpa only [viewAt_number] using data
  · subst other; exact ⟨enrolled, (viewAt_number state message.view).symm⟩

theorem scoped_record (c : Config) (state : State)
    (current deadline now : Nat) (checked : List Block) (offers : List Bytes)
    (outbox : List Message) (audit : List AuditEvent) (delivered : List Block) (tip : Block)
    (needsPoll failed : Bool) :
Scoped c { self := state.self, current := current, deadline := deadline, now := now, views := state.views, checked := checked, offers := offers, outbox := outbox, audit := audit, delivered := delivered, committedTip := tip, needsPoll := needsPoll, failed := failed } ↔ Scoped c state := Iff.rfl

theorem broadcast_scoped {c : Config} {state : State}
    (number : Nat) (kind : Kind) (arg : Argument) (scopeOK : Scoped c state) :
    Scoped c (broadcast state number kind arg) := by
  exact register_scoped ⟨state.self, number, kind, arg⟩ scopeOK scopeOK.1

theorem clear_scoped {c : Config} {state : State}
    (number : Nat) (arg : Argument) (scopeOK : Scoped c state) :
    Scoped c (clear state number arg) := by
  cases arg with
  | none =>
    simp only [clear]
    split
    · exact scopeOK
    · apply (scoped_record ..).mpr
      exact putView_copied_received _ number scopeOK rfl rfl
  | some block =>
    simp only [clear]
    split
    · apply (scoped_record ..).mpr
      exact putView_copied_received _ number scopeOK rfl rfl
    · exact scopeOK

theorem doCommit_scoped {c : Config} {state : State}
    (number : Nat) (block : Block) (scopeOK : Scoped c state) :
    Scoped c (doCommit state number block) := by
  have cleared := clear_scoped number (some block) scopeOK
  have recorded := putView_copied_received
    {viewAt (clear state number (some block)) number with committed := some block}
    number cleared rfl rfl
  unfold doCommit
  dsimp only
  split_ifs <;> first | exact scopeOK | exact cleared | exact recorded

theorem castVote_scoped {c : Config} {state : State}
    (number : Nat) (block : Block) (scopeOK : Scoped c state) :
    Scoped c (castVote state number block) := by
  unfold castVote
  dsimp only
  split
  · exact scopeOK
  · apply broadcast_scoped
    exact putView_copied_received _ number scopeOK rfl rfl

theorem sendCandidate_scoped {c : Config} {state : State}
    (number : Nat) (arg : Argument) (scopeOK : Scoped c state) :
    Scoped c (sendCandidate state number arg) := by
  unfold sendCandidate
  dsimp only
  split
  · exact scopeOK
  · apply broadcast_scoped
    exact putView_copied_received _ number scopeOK rfl rfl

#assert_axioms viewAt_scoped
#assert_axioms register_scoped
#assert_axioms broadcast_scoped
#assert_axioms clear_scoped
#assert_axioms doCommit_scoped
#assert_axioms castVote_scoped
#assert_axioms sendCandidate_scoped
end Minidregg.Kernel.GenericSimplexReceiveScope
