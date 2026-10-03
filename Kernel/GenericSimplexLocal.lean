import Kernel.GenericSimplex
import Mathlib.Data.List.Basic
import Mathlib.Tactic.SplitIfs
import Theory.AssertAxioms
namespace Minidregg.Kernel.GenericSimplexLocal
open Minidregg.Kernel.GenericSimplex
set_option autoImplicit false

/-- Local continuation composition retains exact chronological history and
actor identity. This relation contains no agreement or quorum premise. -/
structure AuditExtension (before after : State) : Prop where
  sameSelf : after.self = before.self
  history : before.audit <+: after.audit

theorem AuditExtension.refl (state : State) : AuditExtension state state :=
  ⟨rfl,List.prefix_rfl⟩

theorem AuditExtension.trans {a b c : State}
    (left : AuditExtension a b) (right : AuditExtension b c) :
    AuditExtension a c :=
  ⟨right.sameSelf.trans left.sameSelf,left.history.trans right.history⟩

theorem foldl_audit_extension {α : Type} (action : State → α → State)
    (each : ∀ state item, AuditExtension state (action state item))
    (items : List α) (state : State) :
    AuditExtension state (items.foldl action state) := by
  induction items generalizing state with
  | nil => exact AuditExtension.refl state
  | cons item rest ih =>
    exact (each state item).trans (ih (action state item))

def eventOwner : AuditEvent → Option Nat
  | .send message => some message.sender
  | .prepare party _ _ | .disable party _ | .commit party _ _ => some party
  | .idle => none

def OwnedAudit (state : State) : Prop :=
  ∀ event ∈ state.audit, eventOwner event = some state.self

theorem append_owned (state : State) (event : AuditEvent)
    (old : OwnedAudit state) (owner : eventOwner event = some state.self) :
    OwnedAudit {state with audit := state.audit ++ [event]} := by
  intro entry member
  rcases List.mem_append.mp member with previous | added
  · exact old entry previous
  · have same : entry = event := by simpa using added
    subst entry
    exact owner

theorem putView_owned (state : State) (view : View) (old : OwnedAudit state) :
    OwnedAudit (putView state view) := old

theorem register_owned (state : State) (message : Message) (old : OwnedAudit state) :
    OwnedAudit (register state message) := old

theorem broadcast_owned (state : State) (number : Nat) (kind : Kind)
    (arg : Argument) (old : OwnedAudit state) :
    OwnedAudit (broadcast state number kind arg) := by
  exact append_owned (register state ⟨state.self,number,kind,arg⟩)
    (.send ⟨state.self,number,kind,arg⟩) (register_owned state _ old) rfl

theorem drain_owned (state : State) (old : OwnedAudit state) :
    OwnedAudit (drainOutbox state).2 := old

/-- The commit lock constrains both earlier and later candidate emissions.
This is a local invariant, not an assumed agreement property. -/
def ViewLock (v : View) : Prop :=
  ∀ block, v.sentCommit = some block →
    ∀ arg ∈ v.sentCandidates, arg = some block
def StateLock (s : State) : Prop := ∀ v ∈ s.views, ViewLock v

theorem default_locked (number : Nat) : ViewLock { number := number } := by
  intro block committed
  cases committed

theorem viewAt_locked (s : State) (number : Nat) (locked : StateLock s) :
    ViewLock (viewAt s number) := by
  unfold viewAt
  cases found : s.views.find? (fun v => v.number == number) with
  | none => exact default_locked number
  | some v => exact locked v (List.mem_of_find?_eq_some found)

theorem putView_locked (s : State) (v : View) (locked : StateLock s)
    (newLocked : ViewLock v) : StateLock (putView s v) := by
  intro w member
  unfold putView at member
  split at member
  · obtain ⟨old, inside, equal⟩ := List.mem_map.mp member
    split at equal
    · subst w; exact newLocked
    · subst w; exact locked old inside
  · rcases List.mem_append.mp member with old | added
    · exact locked w old
    · have same : w = v := by simpa using added
      subst w
      exact newLocked

theorem register_locked (s : State) (m : Message) (locked : StateLock s) :
    StateLock (register s m) := by
  apply putView_locked s _ locked
  exact viewAt_locked s m.view locked

theorem broadcast_locked (s : State) (number : Nat) (kind : Kind)
    (arg : Argument) (locked : StateLock s) :
    StateLock (broadcast s number kind arg) :=
  register_locked s ⟨s.self,number,kind,arg⟩ locked

/-- This is the exact local guard on the COMMIT-producing branch of valueRules;
it includes every candidate already emitted before committing. -/
theorem commit_record_locked (v : View) (block : Block)
    (onlyThis : v.sentCandidates.all (fun arg => arg == some block) = true) :
    ViewLock {v with sentCommit := some block} := by
  intro chosen committed arg member
  have same : block = chosen := Option.some.inj committed
  subst chosen
  have equal := List.all_eq_true.mp onlyThis arg member
  simpa using equal

theorem clear_locked (s : State) (number : Nat) (arg : Argument)
    (locked : StateLock s) : StateLock (clear s number arg) := by
  cases arg with
  | none =>
    simp only [clear]
    split
    · exact locked
    · exact putView_locked s _ locked (viewAt_locked s number locked)
  | some block =>
    simp only [clear]
    split
    · exact putView_locked s _ locked (viewAt_locked s number locked)
    · exact locked

theorem putView_self (s : State) (v : View) : (putView s v).self = s.self := rfl
theorem putView_audit (s : State) (v : View) : (putView s v).audit = s.audit := rfl
theorem register_self (s : State) (m : Message) : (register s m).self = s.self := rfl
theorem register_audit (s : State) (m : Message) : (register s m).audit = s.audit := rfl
theorem clear_self (s : State) (number : Nat) (arg : Argument) :
    (clear s number arg).self = s.self := by
  cases arg <;> simp [clear,putView] <;> split <;> rfl

/-- Audit is persistent protocol history even when a physical sender consumes
the ordinary network outbox. -/
theorem drain_preserves_self (s : State) : (drainOutbox s).2.self = s.self := rfl

theorem sendCandidate_locked (s : State) (number : Nat) (arg : Argument)
    (locked : StateLock s) : StateLock (sendCandidate s number arg) := by
  unfold sendCandidate
  dsimp only
  split
  · exact locked
  next guard =>
    apply broadcast_locked
    apply putView_locked s _ locked
    intro block committed candidate member
    change (viewAt s number).sentCommit = some block at committed
    rcases List.mem_append.mp member with old | added
    · exact viewAt_locked s number locked block committed candidate old
    · have same : candidate = arg := by simpa using added
      subst candidate
      by_contra different
      have rejected : ((viewAt s number).sentCandidates.contains arg ||
          ((viewAt s number).sentCommit.isSome &&
            (viewAt s number).sentCommit != arg)) = true := by
        simp [committed, Ne.symm different]
      exact guard rejected

/-- Every concrete broadcast appends exactly one auditable event, in causal order.
The statement uses the executable outbox, rather than an independently modelled
set of sent messages. The audit below survives actual outbox draining. -/
theorem broadcast_emission (s : State) (number : Nat) (kind : Kind) (arg : Argument) :
    (broadcast s number kind arg).outbox =
      s.outbox ++ [⟨s.self,number,kind,arg⟩] := by
  simp [broadcast, register, putView]

theorem broadcast_self (s : State) (number : Nat) (kind : Kind) (arg : Argument) :
    (broadcast s number kind arg).self = s.self := by
  simp [broadcast, register, putView]

theorem sendCandidate_rejected_by_commit (s : State) (number : Nat)
    (arg : Argument) (block : Block)
    (committed : (viewAt s number).sentCommit = some block)
    (different : arg ≠ some block) : sendCandidate s number arg = s := by
  simp [sendCandidate, committed, Ne.symm different]

theorem clear_owned (s : State) (number : Nat) (arg : Argument)
    (owned : OwnedAudit s) : OwnedAudit (clear s number arg) := by
  cases arg with
  | none =>
    simp only [clear]
    split
    · exact owned
    · exact append_owned (putView s {viewAt s number with disabled := true})
        (.disable s.self number) (putView_owned s _ owned) rfl
  | some block =>
    simp only [clear]
    split
    · exact append_owned
        (putView s {viewAt s number with
          prepared := (viewAt s number).prepared ++ [block]})
        (.prepare s.self number block) (putView_owned s _ owned) rfl
    · exact owned

theorem doCommit_self (s : State) (number : Nat) (block : Block) :
    (doCommit s number block).self = s.self := by
  unfold doCommit
  dsimp only
  split_ifs <;> simp_all [putView,clear_self]

theorem doCommit_owned (s : State) (number : Nat) (block : Block)
    (owned : OwnedAudit s) : OwnedAudit (doCommit s number block) := by
  have cleared := clear_owned s number (some block) owned
  unfold doCommit
  dsimp only
  split_ifs <;> simp_all [OwnedAudit,putView,eventOwner,clear_self]
  all_goals
    intro event member
    rcases member with old | same
    · exact cleared event old
    · subst event; rfl

theorem doCommit_audit_prefix (s : State) (number : Nat) (block : Block) :
    s.audit <+: (doCommit s number block).audit := by
  unfold doCommit clear
  dsimp only
  split_ifs <;> simp_all [putView,List.append_assoc]

theorem sendCandidate_self (s : State) (number : Nat) (arg : Argument) :
    (sendCandidate s number arg).self = s.self := by
  unfold sendCandidate
  dsimp only
  split
  · rfl
  · simp [broadcast,register,putView]

theorem castVote_self (s : State) (number : Nat) (block : Block) :
    (castVote s number block).self = s.self := by
  unfold castVote
  dsimp only
  split
  · rfl
  · simp [broadcast,register,putView]

theorem castVote_owned (s : State) (number : Nat) (block : Block)
    (owned : OwnedAudit s) : OwnedAudit (castVote s number block) := by
  unfold castVote
  dsimp only
  split
  · exact owned
  · exact broadcast_owned (putView s {viewAt s number with voted := true})
      number .vote (some block) (putView_owned s _ owned)

theorem sendCandidate_owned (s : State) (number : Nat) (arg : Argument)
    (owned : OwnedAudit s) : OwnedAudit (sendCandidate s number arg) := by
  unfold sendCandidate
  dsimp only
  split
  · exact owned
  · exact broadcast_owned
      (putView s {viewAt s number with
        sentCandidates := (viewAt s number).sentCandidates ++ [arg]})
      number .candidate arg (putView_owned s _ owned)

theorem clear_audit_prefix (s : State) (number : Nat) (arg : Argument) :
    s.audit <+: (clear s number arg).audit := by
  cases arg <;> simp only [clear] <;> split <;> simp [putView]

theorem broadcast_audit_prefix (s : State) (number : Nat) (kind : Kind)
    (arg : Argument) : s.audit <+: (broadcast s number kind arg).audit := by
  simp [broadcast,register,putView]

theorem sendCandidate_audit_prefix (s : State) (number : Nat) (arg : Argument) :
    s.audit <+: (sendCandidate s number arg).audit := by
  unfold sendCandidate
  dsimp only
  split
  · exact List.prefix_rfl
  · simpa [putView] using
      broadcast_audit_prefix
        (putView s { viewAt s number with
          sentCandidates := (viewAt s number).sentCandidates ++ [arg] })
        number .candidate arg

theorem castVote_audit_prefix (s : State) (number : Nat) (block : Block) :
    s.audit <+: (castVote s number block).audit := by
  unfold castVote
  dsimp only
  split
  · exact List.prefix_rfl
  · simpa [putView] using broadcast_audit_prefix
      (putView s {viewAt s number with voted := true}) number .vote (some block)

theorem broadcast_audit (s : State) (number : Nat) (kind : Kind) (arg : Argument) :
    (broadcast s number kind arg).audit =
      s.audit ++ [.send ⟨s.self,number,kind,arg⟩] := by
  simp [broadcast, register, putView]

theorem drain_preserves_audit (s : State) :
    (drainOutbox s).2.audit = s.audit := rfl

#assert_axioms clear_owned
#assert_axioms doCommit_self
#assert_axioms doCommit_owned
#assert_axioms doCommit_audit_prefix
#assert_axioms sendCandidate_self
#assert_axioms castVote_self
#assert_axioms castVote_owned
#assert_axioms sendCandidate_owned
#assert_axioms append_owned
#assert_axioms broadcast_owned
#assert_axioms drain_owned
#assert_axioms AuditExtension.trans
#assert_axioms foldl_audit_extension
#assert_axioms clear_audit_prefix
#assert_axioms broadcast_audit_prefix
#assert_axioms sendCandidate_audit_prefix
#assert_axioms castVote_audit_prefix
#assert_axioms commit_record_locked
#assert_axioms clear_locked
#assert_axioms clear_self
#assert_axioms putView_self
#assert_axioms putView_audit
#assert_axioms register_self
#assert_axioms register_audit
#assert_axioms drain_preserves_self
#assert_axioms sendCandidate_locked
#assert_axioms broadcast_audit
#assert_axioms drain_preserves_audit
#assert_axioms viewAt_locked
#assert_axioms putView_locked
#assert_axioms register_locked
#assert_axioms broadcast_locked
#assert_axioms broadcast_emission
#assert_axioms broadcast_self
#assert_axioms sendCandidate_rejected_by_commit
end Minidregg.Kernel.GenericSimplexLocal
