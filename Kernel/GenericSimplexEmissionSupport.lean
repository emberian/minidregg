import Kernel.GenericSimplexCountSupport
import Kernel.GenericSimplexReceiveProvenance
import Kernel.GenericSimplexReceiveScope

namespace Minidregg.Kernel.GenericSimplexEmissionSupport
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexLocal
open Minidregg.Kernel.GenericSimplexCountSupport
open Minidregg.Kernel.GenericSimplexReceiveProvenance
open Minidregg.Kernel.GenericSimplexReceiveScope
set_option autoImplicit false

/-- Finite, deduplicated voters backed by an authenticated external arrival or
an actual retained SEND in the specified prefix. This asserts no agreement. -/
def EvidenceSupport (external : Message → Prop) (history : List AuditEvent)
    (roster : Finset Nat) (view : Nat) (kind : Kind) (arg : Argument) (threshold : Nat) : Prop :=
  ∃ voters : Finset Nat, voters ⊆ roster ∧ threshold ≤ voters.card ∧
    ∀ party ∈ voters, external ⟨party, view, kind, arg⟩ ∨
      .send ⟨party, view, kind, arg⟩ ∈ history

theorem actual_count_evidence (c : Config) (s : State) (external : Message → Prop)
    (scopeOK : Scoped c s) (backed : Backed external s)
    (view : Nat) (kind : Kind) (arg : Argument) (threshold : Nat)
    (enough : threshold ≤ count (viewAt s view) kind arg) :
    EvidenceSupport external s.audit (Finset.range c.parties) view kind arg threshold := by
  refine ⟨(countedSenders (viewAt s view) kind arg).toFinset, ?_, ?_, ?_⟩
  · intro party member
    obtain ⟨message, inside, sender, _, _⟩ := counted_sender_received (List.mem_toFinset.mp member)
    have bound := (viewAt_scoped scopeOK view message inside).1
    simpa only [sender, Finset.mem_range] using bound
  · simpa only [count_is_distinct_card] using enough
  · intro party member
    obtain ⟨message, inside, sender, kindEq, argEq⟩ :=
      counted_sender_received (List.mem_toFinset.mp member)
    have viewEq := (viewAt_scoped scopeOK view message inside).2
    have available := viewAt_backed backed view message inside
    have exact : message = ⟨party, view, kind, arg⟩ := by
      cases message
      simp_all
    simpa only [exact] using available

def EventSupported (c : Config) (external : Message → Prop)
    (roster : Finset Nat) (priorEvents : List AuditEvent) : AuditEvent → Prop
  | .send message => match message.kind, message.value with
      | .commit, some block => EvidenceSupport external priorEvents roster message.view .vote (some block) c.quorum
      | .candidate, some block => EvidenceSupport external priorEvents roster message.view .vote (some block) (c.faults + 1)
      | .ready, arg => EvidenceSupport external priorEvents roster message.view .candidate arg c.quorum ∨
          EvidenceSupport external priorEvents roster message.view .ready arg (c.faults + 1)
      | _, _ => True
  | .prepare _ view block => EvidenceSupport external priorEvents roster view .vote (some block) c.quorum ∨
      EvidenceSupport external priorEvents roster view .ready (some block) c.quorum ∨
      EvidenceSupport external priorEvents roster view .commit (some block) c.quorum
  | .disable _ view => EvidenceSupport external priorEvents roster view .ready none c.quorum
  | .commit _ view block => EvidenceSupport external priorEvents roster view .commit (some block) c.quorum
  | .idle => True

/-- Every retained emission is justified on the STRICT prefix before its own
index. A whole-post-state support witness is deliberately insufficient. -/
def EmissionJustified (c : Config) (external : Message → Prop)
    (roster : Finset Nat) (history : List AuditEvent) : Prop :=
  ∀ index (within : index < history.length),
    EventSupported c external roster (history.take index) history[index]

theorem evidence_weaken {external next : Message → Prop}
    {history : List AuditEvent} {roster : Finset Nat} {view threshold : Nat}
    {kind : Kind} {arg : Argument}
    (support : EvidenceSupport external history roster view kind arg threshold)
    (widen : ∀ message, external message → next message) :
    EvidenceSupport next history roster view kind arg threshold := by
  obtain ⟨voters, members, enough, available⟩ := support
  exact ⟨voters, members, enough, fun party member => (available party member).imp (widen _) id⟩

theorem evidence_prefix {external : Message → Prop}
    {before after : List AuditEvent} {roster : Finset Nat} {view threshold : Nat}
    {kind : Kind} {arg : Argument}
    (support : EvidenceSupport external before roster view kind arg threshold)
    (extension : before <+: after) : EvidenceSupport external after roster view kind arg threshold := by
  obtain ⟨voters, members, enough, available⟩ := support
  exact ⟨voters, members, enough, fun party member =>
    (available party member).imp id (fun sent => extension.sublist.subset sent)⟩

/-- One actual append requires its cause on the old prefix. Earlier events
retain their exact original take-prefix; later evidence cannot justify them. -/
theorem emission_append (c : Config) (external : Message → Prop) (roster : Finset Nat)
    (history : List AuditEvent) (event : AuditEvent)
    (old : EmissionJustified c external roster history)
    (fresh : EventSupported c external roster history event) :
    EmissionJustified c external roster (history ++ [event]) := by
  intro index within
  by_cases previous : index < history.length
  · rw [List.take_append_of_le_length (Nat.le_of_lt previous)]
    simpa only [List.getElem_append_left previous] using old index previous
  · have last : index = history.length := by
      simp only [List.length_append, List.length_singleton] at within
      omega
    subst index
    simpa using fresh

#assert_axioms emission_append

#assert_axioms actual_count_evidence
#assert_axioms evidence_weaken
#assert_axioms evidence_prefix
theorem event_weaken {c : Config} {external next : Message → Prop}
    {roster : Finset Nat} {history : List AuditEvent} {event : AuditEvent}
    (supported : EventSupported c external roster history event)
    (widen : ∀ message, external message → next message) :
    EventSupported c next roster history event := by
  cases event with
  | send message =>
      cases message with
      | mk sender view kind arg =>
          cases kind <;> cases arg <;> simp only [EventSupported] at supported ⊢
          all_goals first
            | exact True.intro
            | exact evidence_weaken supported widen
            | exact supported.imp (fun h => evidence_weaken h widen) (fun h => evidence_weaken h widen)
  | prepare party view block =>
      exact supported.imp (fun h => evidence_weaken h widen)
        (fun h => h.imp (fun h => evidence_weaken h widen) (fun h => evidence_weaken h widen))
  | disable party view => exact evidence_weaken supported widen
  | commit party view block => exact evidence_weaken supported widen
  | idle => exact True.intro

theorem emission_weaken {c : Config} {external next : Message → Prop}
    {roster : Finset Nat} {history : List AuditEvent}
    (old : EmissionJustified c external roster history)
    (widen : ∀ message, external message → next message) :
    EmissionJustified c next roster history := by
  intro index within
  exact event_weaken (old index within) widen

theorem emission_empty (c : Config) (external : Message → Prop) (roster : Finset Nat) :
    EmissionJustified c external roster [] := by
  intro index within
  simp at within

/-- This preserves a real broadcast only when its cause was already available
before register adds the newly emitted message to local received storage. -/
theorem broadcast_emission (c : Config) (external : Message → Prop) (roster : Finset Nat)
    (s : State) (view : Nat) (kind : Kind) (arg : Argument)
    (old : EmissionJustified c external roster s.audit)
    (cause : EventSupported c external roster s.audit (.send ⟨s.self, view, kind, arg⟩)) :
    EmissionJustified c external roster (broadcast s view kind arg).audit := by
  change EmissionJustified c external roster (s.audit ++ [.send ⟨s.self, view, kind, arg⟩])
  exact emission_append c external roster s.audit _ old cause

#assert_axioms event_weaken
#assert_axioms emission_weaken
#assert_axioms emission_empty
#assert_axioms broadcast_emission

/-- Exact executable COMMIT guard yields support before the send is registered. -/
theorem commit_send_cause (c : Config) (s : State) (external : Message → Prop)
    (scopeOK : Scoped c s) (backed : Backed external s) (view : Nat) (block : Block)
    (enough : c.quorum ≤ count (viewAt s view) .vote (some block)) :
    EventSupported c external (Finset.range c.parties) s.audit
      (.send ⟨s.self, view, .commit, some block⟩) :=
  actual_count_evidence c s external scopeOK backed view .vote (some block) c.quorum enough

theorem candidate_send_cause (c : Config) (s : State) (external : Message → Prop)
    (scopeOK : Scoped c s) (backed : Backed external s) (view : Nat) (block : Block)
    (enough : c.faults + 1 ≤ count (viewAt s view) .vote (some block)) :
    EventSupported c external (Finset.range c.parties) s.audit
      (.send ⟨s.self, view, .candidate, some block⟩) :=
  actual_count_evidence c s external scopeOK backed view .vote (some block) (c.faults + 1) enough

theorem ready_send_cause (c : Config) (s : State) (external : Message → Prop)
    (scopeOK : Scoped c s) (backed : Backed external s) (view : Nat) (arg : Argument)
    (enough : c.quorum ≤ count (viewAt s view) .candidate arg ∨
      c.faults + 1 ≤ count (viewAt s view) .ready arg) :
    EventSupported c external (Finset.range c.parties) s.audit
      (.send ⟨s.self, view, .ready, arg⟩) := by
  exact enough.imp
    (actual_count_evidence c s external scopeOK backed view .candidate arg c.quorum)
    (actual_count_evidence c s external scopeOK backed view .ready arg (c.faults + 1))

#assert_axioms commit_send_cause
#assert_axioms candidate_send_cause
#assert_axioms ready_send_cause
theorem clear_emission (c : Config) (external : Message → Prop) (roster : Finset Nat)
    (s : State) (view : Nat) (arg : Argument)
    (old : EmissionJustified c external roster s.audit)
    (cause : match arg with
      | none => EventSupported c external roster s.audit (.disable s.self view)
      | some block => EventSupported c external roster s.audit (.prepare s.self view block)) :
    EmissionJustified c external roster (clear s view arg).audit := by
  cases arg with
  | none =>
      simp only [clear]
      split
      · exact old
      · change EmissionJustified c external roster (s.audit ++ [.disable s.self view])
        exact emission_append c external roster s.audit _ old cause
  | some block =>
      simp only [clear]
      split
      · change EmissionJustified c external roster (s.audit ++ [.prepare s.self view block])
        exact emission_append c external roster s.audit _ old cause
      · exact old

theorem event_prefix {c : Config} {external : Message → Prop}
    {roster : Finset Nat} {before after : List AuditEvent} {event : AuditEvent}
    (supported : EventSupported c external roster before event)
    (extension : before <+: after) : EventSupported c external roster after event := by
  cases event with
  | send message =>
      cases message with
      | mk sender view kind arg =>
          cases kind <;> cases arg <;> simp only [EventSupported] at supported ⊢
          all_goals first
            | exact True.intro
            | exact evidence_prefix supported extension
            | exact supported.imp (fun h => evidence_prefix h extension) (fun h => evidence_prefix h extension)
  | prepare party view block =>
      exact supported.imp (fun h => evidence_prefix h extension)
        (fun h => h.imp (fun h => evidence_prefix h extension) (fun h => evidence_prefix h extension))
  | disable party view => exact evidence_prefix supported extension
  | commit party view block => exact evidence_prefix supported extension
  | idle => exact True.intro

#assert_axioms clear_emission
#assert_axioms event_prefix
theorem doCommit_emission (c : Config) (external : Message → Prop) (roster : Finset Nat)
    (s : State) (view : Nat) (block : Block)
    (old : EmissionJustified c external roster s.audit)
    (cause : EventSupported c external roster s.audit (.commit s.self view block)) :
    EmissionJustified c external roster (doCommit s view block).audit := by
  have prepared : EventSupported c external roster s.audit (.prepare s.self view block) :=
    Or.inr (Or.inr cause)
  have cleared := clear_emission c external roster s view (some block) old prepared
  have committed : EmissionJustified c external roster
      ((clear s view (some block)).audit ++ [.commit s.self view block]) :=
    emission_append c external roster _ _ cleared
      (event_prefix cause (clear_audit_prefix s view (some block)))
  unfold doCommit
  split
  · exact old
  · dsimp only
    split
    · exact cleared
    · split
      · split <;> simpa only [putView_audit, putView_self, clear_self] using committed
      · split <;> simpa only [putView_audit, putView_self, clear_self] using committed

#assert_axioms doCommit_emission
theorem sendCandidate_emission (c : Config) (external : Message → Prop) (roster : Finset Nat)
    (s : State) (view : Nat) (arg : Argument)
    (old : EmissionJustified c external roster s.audit)
    (cause : EventSupported c external roster s.audit (.send ⟨s.self, view, .candidate, arg⟩)) :
    EmissionJustified c external roster (sendCandidate s view arg).audit := by
  unfold sendCandidate
  dsimp only
  split
  · exact old
  · apply broadcast_emission
    · exact old
    · exact cause

theorem castVote_emission (c : Config) (external : Message → Prop) (roster : Finset Nat)
    (s : State) (view : Nat) (block : Block)
    (old : EmissionJustified c external roster s.audit) :
    EmissionJustified c external roster (castVote s view block).audit := by
  unfold castVote
  dsimp only
  split
  · exact old
  · apply broadcast_emission
    · exact old
    · exact True.intro

#assert_axioms sendCandidate_emission
#assert_axioms castVote_emission
/-- The real value-rule path clears first, then optionally sends COMMIT.
Its cause comes from the original VOTE tally, not from the new broadcast. -/
theorem clear_commit_emission (c : Config) (external : Message → Prop)
    (s : State) (view : Nat) (block : Block)
    (scopeOK : Scoped c s) (backed : Backed external s)
    (old : EmissionJustified c external (Finset.range c.parties) s.audit)
    (enough : c.quorum ≤ count (viewAt s view) .vote (some block)) :
    let cleared := clear s view (some block)
    let v := viewAt cleared view
    let selected := if v.sentCommit.isNone && v.sentCandidates.all (fun a => a == some block) then
      broadcast (putView cleared {v with sentCommit := some block}) view .commit (some block)
      else cleared
    EmissionJustified c external (Finset.range c.parties) selected.audit := by
  have evidence := actual_count_evidence c s external scopeOK backed view .vote (some block) c.quorum enough
  have prepared := clear_emission c external (Finset.range c.parties) s view (some block) old (Or.inl evidence)
  have later := evidence_prefix evidence (clear_audit_prefix s view (some block))
  dsimp only
  split
  · apply broadcast_emission
    · exact prepared
    · simpa only [putView_self, putView_audit, clear_self, EventSupported] using later
  · exact prepared

#assert_axioms clear_commit_emission
structure EmissionInvariant (c : Config) (external : Message → Prop) (s : State) : Prop where
  scopeOK : Scoped c s
  backed : Backed external s
  emitted : EmissionJustified c external (Finset.range c.parties) s.audit

theorem putCopied_invariant {c : Config} {external : Message → Prop} {s : State}
    (view : Nat) (updated : View) (old : EmissionInvariant c external s)
    (number : updated.number = (viewAt s view).number)
    (received : updated.received = (viewAt s view).received) :
    EmissionInvariant c external (putView s updated) :=
  ⟨putView_copied_received updated view old.scopeOK number received,
    putView_received_unchanged view updated old.backed received, old.emitted⟩

theorem broadcast_invariant {c : Config} {external : Message → Prop} {s : State}
    (view : Nat) (kind : Kind) (arg : Argument) (old : EmissionInvariant c external s)
    (cause : EventSupported c external (Finset.range c.parties) s.audit
      (.send ⟨s.self, view, kind, arg⟩)) :
    EmissionInvariant c external (broadcast s view kind arg) :=
  ⟨broadcast_scoped view kind arg old.scopeOK,
    broadcast_backed view kind arg old.backed,
    broadcast_emission c external _ s view kind arg old.emitted cause⟩

theorem clear_invariant {c : Config} {external : Message → Prop} {s : State}
    (view : Nat) (arg : Argument) (old : EmissionInvariant c external s)
    (cause : match arg with
      | none => EventSupported c external (Finset.range c.parties) s.audit (.disable s.self view)
      | some block => EventSupported c external (Finset.range c.parties) s.audit (.prepare s.self view block)) :
    EmissionInvariant c external (clear s view arg) :=
  ⟨clear_scoped view arg old.scopeOK, clear_backed view arg old.backed,
    clear_emission c external _ s view arg old.emitted cause⟩

theorem doCommit_invariant {c : Config} {external : Message → Prop} {s : State}
    (view : Nat) (block : Block) (old : EmissionInvariant c external s)
    (enough : c.quorum ≤ count (viewAt s view) .commit (some block)) :
    EmissionInvariant c external (doCommit s view block) :=
  ⟨doCommit_scoped view block old.scopeOK, doCommit_backed view block old.backed,
    doCommit_emission c external _ s view block old.emitted
      (actual_count_evidence c s external old.scopeOK old.backed view .commit (some block) c.quorum enough)⟩

theorem candidate_invariant {c : Config} {external : Message → Prop} {s : State}
    (view : Nat) (arg : Argument) (old : EmissionInvariant c external s)
    (enough : match arg with
      | none => True
      | some block => c.faults + 1 ≤ count (viewAt s view) .vote (some block)) :
    EmissionInvariant c external (sendCandidate s view arg) := by
  refine ⟨sendCandidate_scoped view arg old.scopeOK,
    sendCandidate_backed view arg old.backed,
    sendCandidate_emission c external _ s view arg old.emitted ?_⟩
  cases arg with
  | none => exact True.intro
  | some block => exact candidate_send_cause c s external old.scopeOK old.backed view block enough

#assert_axioms putCopied_invariant
#assert_axioms broadcast_invariant
#assert_axioms clear_invariant
#assert_axioms doCommit_invariant
#assert_axioms candidate_invariant
theorem votePhase_invariant {c : Config} {external : Message → Prop} {s : State}
    (view : Nat) (block : Block) (old : EmissionInvariant c external s) :
    EmissionInvariant c external
      (if count (viewAt s view) .vote (some block) ≥ c.quorum && validBlock s block then
        let cleared := clear s view (some block)
        let v := viewAt cleared view
        if v.sentCommit.isNone && v.sentCandidates.all (fun a => a == some block) then
          broadcast (putView cleared {v with sentCommit := some block}) view .commit (some block)
        else cleared
      else s) := by
  split
  next enabled =>
    have enough : c.quorum ≤ count (viewAt s view) .vote (some block) := by
      simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at enabled
      exact enabled.1
    have support := actual_count_evidence c s external old.scopeOK old.backed view .vote (some block) c.quorum enough
    have cleared := clear_invariant view (some block) old (Or.inl support)
    have later := evidence_prefix support (clear_audit_prefix s view (some block))
    dsimp only
    split
    · apply broadcast_invariant
      · exact putCopied_invariant view _ cleared rfl rfl
      · simpa only [EventSupported, putView_audit, putView_self, clear_self] using later
    · exact cleared
  · exact old

theorem valueRules_invariant (c : Config) (external : Message → Prop) (s : State)
    (view : Nat) (block : Block) (old : EmissionInvariant c external s) :
    EmissionInvariant c external (valueRules c s view block) := by
  let phase := if count (viewAt s view) .vote (some block) ≥ c.quorum && validBlock s block then
        let cleared := clear s view (some block)
        let v := viewAt cleared view
        if v.sentCommit.isNone && v.sentCandidates.all (fun a => a == some block) then
          broadcast (putView cleared {v with sentCommit := some block}) view .commit (some block)
        else cleared
      else s
  have phaseInv : EmissionInvariant c external phase := votePhase_invariant view block old
  let afterCommit := if count (viewAt phase view) .commit (some block) ≥ c.quorum then
      doCommit phase view block else phase
  have commitInv : EmissionInvariant c external afterCommit := by
    dsimp only [afterCommit]
    split
    · apply doCommit_invariant view block phaseInv
      assumption
    · exact phaseInv
  have equation : valueRules c s view block =
    (if count (viewAt afterCommit view) .vote (some block) ≥ c.faults + 1 &&
      validBlock afterCommit block then sendCandidate afterCommit view (some block) else afterCommit) := by
    simp only [valueRules, Id.run, bind, pure, afterCommit, phase]
    split_ifs <;> rfl
  rw [equation]
  split
  next enabled =>
    apply candidate_invariant view (some block) commitInv
    simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at enabled
    exact enabled.1
  · exact commitInv

#assert_axioms votePhase_invariant
#assert_axioms valueRules_invariant
theorem argumentRules_invariant (c : Config) (external : Message → Prop) (s : State)
    (view : Nat) (arg : Argument) (size : c.parties = 3 * c.faults + 1)
    (old : EmissionInvariant c external s) :
    EmissionInvariant c external (argumentRules c s view arg) := by
  have quorum : c.quorum = 2 * c.faults + 1 := by
    simp only [Config.quorum, size]
    omega
  let core := if count (viewAt s view) .candidate arg ≥ 2 * c.faults + 1 &&
      !(viewAt s view).sentReadyCore.contains arg then
        broadcast (putView s {viewAt s view with sentReadyCore :=
          (viewAt s view).sentReadyCore ++ [arg]}) view .ready arg else s
  have coreInv : EmissionInvariant c external core := by
    dsimp only [core]
    split
    next enabled =>
      simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at enabled
      apply broadcast_invariant
      · exact putCopied_invariant view _ old rfl rfl
      · apply Or.inl
        simpa only [putView_audit, quorum] using
          actual_count_evidence c s external old.scopeOK old.backed view .candidate arg
            (2 * c.faults + 1) enabled.1
    · exact old
  let relay := if count (viewAt core view) .ready arg ≥ c.faults + 1 &&
      !(viewAt core view).sentReadyRelay.contains arg then
        broadcast (putView core {viewAt core view with sentReadyRelay :=
          (viewAt core view).sentReadyRelay ++ [arg]}) view .ready arg else core
  have relayInv : EmissionInvariant c external relay := by
    dsimp only [relay]
    split
    next enabled =>
      simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at enabled
      apply broadcast_invariant
      · exact putCopied_invariant view _ coreInv rfl rfl
      · apply Or.inr
        exact actual_count_evidence c core external coreInv.scopeOK coreInv.backed
          view .ready arg (c.faults + 1) enabled.1
    · exact coreInv
  have equation : argumentRules c s view arg =
      (if count (viewAt relay view) .ready arg ≥ 2 * c.faults + 1 then
        clear relay view arg else relay) := by
    simp only [argumentRules, Id.run, bind, pure, relay, core]
    split_ifs <;> rfl
  rw [equation]
  split
  next enough =>
    have support := actual_count_evidence c relay external relayInv.scopeOK relayInv.backed
      view .ready arg c.quorum (by simpa only [quorum] using enough)
    apply clear_invariant view arg relayInv
    cases arg with
    | none => exact support
    | some block => exact Or.inr (Or.inl support)
  · exact relayInv

#assert_axioms argumentRules_invariant
@[simp] theorem emission_record (c : Config) (external : Message → Prop) (s : State)
    (current deadline now : Nat) (checked : List Block) (offers : List Bytes) (outbox : List Message)
    (delivered : List Block) (tip : Block) (needsPoll failed : Bool) :
    EmissionInvariant c external { self := s.self, current := current, deadline := deadline, now := now, views := s.views, checked := checked, offers := offers, outbox := outbox, audit := s.audit, delivered := delivered, committedTip := tip, needsPoll := needsPoll, failed := failed } ↔
      EmissionInvariant c external s := by
  constructor <;> intro old <;> rcases old with ⟨scopeOK, backed, emitted⟩ <;>
    exact ⟨scopeOK, backed, emitted⟩

theorem castVote_invariant {c : Config} {external : Message → Prop} {s : State}
    (view : Nat) (block : Block) (old : EmissionInvariant c external s) :
    EmissionInvariant c external (castVote s view block) :=
  ⟨castVote_scoped view block old.scopeOK, castVote_backed view block old.backed,
    castVote_emission c external _ s view block old.emitted⟩

theorem proposeSend_invariant {c : Config} {external : Message → Prop} {s : State}
    (view : Nat) (arg : Argument) (old : EmissionInvariant c external s) :
    EmissionInvariant c external (broadcast s view .propose arg) :=
  broadcast_invariant view .propose arg old True.intro

theorem emission_fold {α : Type} {c : Config} {external : Message → Prop}
    (action : State → α → State)
    (each : ∀ state item, EmissionInvariant c external state → EmissionInvariant c external (action state item))
    (items : List α) (s : State) (old : EmissionInvariant c external s) :
    EmissionInvariant c external (items.foldl action s) := by
  induction items generalizing s with
  | nil => exact old
  | cons item rest ih => exact ih (action s item) (each s item old)

theorem progressView_invariant (c : Config) (external : Message → Prop) (s : State)
    (view : Nat) (size : c.parties = 3 * c.faults + 1) (old : EmissionInvariant c external s) :
    EmissionInvariant c external (progressView c s view) := by
  simp only [progressView, Id.run, bind, pure]
  apply emission_fold
  · intro state arg prior; exact argumentRules_invariant c external state view arg size prior
  · apply emission_fold
    · intro state block prior; exact valueRules_invariant c external state view block prior
    · exact old

macro "emission_basic_step" : tactic => `(tactic|
  first
    | assumption
    | fail_if_no_progress simp only [emission_record]
    | with_reducible apply castVote_invariant
    | with_reducible apply proposeSend_invariant
    | (with_reducible apply putCopied_invariant _ _ <;> try rfl)
    | solve | simp_all [viewAt_number]
    | split)
macro "emission_basic_chain" : tactic => `(tactic| repeat' emission_basic_step)

theorem propose_invariant {c : Config} (external : Message → Prop) (s : State)
    (old : EmissionInvariant c external s) :
    EmissionInvariant c external (propose s) := by
  unfold propose
  dsimp only
  emission_basic_chain

theorem enterView_invariant (c : Config) (external : Message → Prop) (s : State)
    (view : Nat) (old : EmissionInvariant c external s) :
    EmissionInvariant c external (enterView c s view) := by
  unfold enterView
  dsimp only
  split
  · apply propose_invariant
    emission_basic_chain
  · emission_basic_chain

theorem progressOuter_invariant (c : Config) (external : Message → Prop) (s : State)
    (old : EmissionInvariant c external s) :
    EmissionInvariant c external (progressOuter c s) := by
  simp only [progressOuter, Id.run, bind, pure]
  repeat' first
    | with_reducible apply enterView_invariant
    | emission_basic_step

theorem pass_invariant (c : Config) (external : Message → Prop) (s : State)
    (size : c.parties = 3 * c.faults + 1) (old : EmissionInvariant c external s) :
    EmissionInvariant c external (pass c s) := by
  unfold pass
  apply progressOuter_invariant
  apply emission_fold
  · intro state view prior; exact progressView_invariant c external state view size prior
  · exact old

theorem pump_invariant (c : Config) (external : Message → Prop) (fuel : Nat) (s : State)
    (size : c.parties = 3 * c.faults + 1) (old : EmissionInvariant c external s) :
    EmissionInvariant c external (pump c fuel s) := by
  induction fuel generalizing s with
  | zero => simpa only [pump, emission_record] using old
  | succ fuel ih =>
    simp only [pump]
    split
    · apply pass_invariant c external _ size
      simpa only [emission_record] using old
    · apply ih
      apply pass_invariant c external _ size
      simpa only [emission_record] using old

#assert_axioms emission_record
#assert_axioms castVote_invariant
#assert_axioms proposeSend_invariant
#assert_axioms emission_fold
#assert_axioms progressView_invariant
#assert_axioms propose_invariant
#assert_axioms enterView_invariant
#assert_axioms progressOuter_invariant
#assert_axioms pass_invariant
#assert_axioms pump_invariant
theorem register_invariant {c : Config} {external : Message → Prop} {s : State}
    (message : Message) (old : EmissionInvariant c external s)
    (enrolled : message.sender < c.parties) (available : external message) :
    EmissionInvariant c external (register s message) :=
  ⟨register_scoped message old.scopeOK enrolled,
    register_backed message old.backed (Or.inl available), old.emitted⟩

theorem ingest_invariant (c : Config) (external : Message → Prop) (s : State)
    (message : Message) (old : EmissionInvariant c external s) (available : external message) :
    EmissionInvariant c external (ingest c s message) := by
  unfold ingest
  dsimp only
  repeat' first
    | (with_reducible apply register_invariant message old <;> first | assumption | simp_all <;> omega)
    | emission_basic_step

def InputAvailable (external : Message → Prop) : Input → Prop
  | .delivery message | .deliveryAt _ message => external message
  | _ => True

theorem step_invariant (c : Config) (external : Message → Prop) (s : State) (input : Input)
    (size : c.parties = 3 * c.faults + 1) (old : EmissionInvariant c external s)
    (available : InputAvailable external input) :
    EmissionInvariant c external (step c s input) := by
  unfold step
  dsimp only
  split
  · emission_basic_chain
  · apply pump_invariant c external _ _ size
    cases input with
    | delivery message => exact ingest_invariant c external s message old available
    | deliveryAt now message =>
      apply ingest_invariant
      · simpa only [emission_record] using old
      · exact available
    | checked block => dsimp only; emission_basic_chain
    | offer payload => dsimp only; emission_basic_chain
    | poll => exact old
    | tick now =>
      dsimp only
      repeat' first
        | with_reducible apply pump_invariant c external _ _ size
        | with_reducible apply candidate_invariant
        | emission_basic_step

theorem initial_invariant (c : Config) (external : Message → Prop)
    (self now deadline : Nat) (offers : List Bytes) (checked : List Block)
    (enrolled : self < c.parties) :
    EmissionInvariant c external
      {self := self, now := now, deadline := deadline, offers := offers, checked := checked} := by
  constructor
  · exact ⟨enrolled, by simp⟩
  · intro view member; simp at member
  · exact emission_empty c external _

theorem start_emission (c : Config) (self now : Nat) (offers : List Bytes) (checked : List Block) :
    EmissionJustified c (fun _ => False) (Finset.range c.parties)
      (start c self now offers checked).audit := by
  unfold start
  split
  · exact emission_empty c (fun _ => False) _
  next admitted =>
    have configOK : c.wellFormed = true := by
      cases h : c.wellFormed <;> simp_all
    have size : c.parties = 3 * c.faults + 1 := by
      have h := configOK
      simp [Config.wellFormed] at h
      exact h.1.1
    have enrolled : self < c.parties := by
      simpa [configOK] using admitted
    exact (pump_invariant c (fun _ => False) _ _ size
      (enterView_invariant c (fun _ => False) _ 1
        (initial_invariant c (fun _ => False) self now (now + c.timeout) offers checked enrolled))).emitted

theorem step_emission (c : Config) (external : Message → Prop) (s : State) (input : Input)
    (size : c.parties = 3 * c.faults + 1)
    (scopeOK : Scoped c s) (backed : Backed external s)
    (old : EmissionJustified c external (Finset.range c.parties) s.audit)
    (available : InputAvailable external input) :
    EmissionJustified c external (Finset.range c.parties) (step c s input).audit :=
  (step_invariant c external s input size ⟨scopeOK, backed, old⟩ available).emitted

#assert_axioms register_invariant
#assert_axioms ingest_invariant
#assert_axioms step_invariant
#assert_axioms initial_invariant
#assert_axioms start_emission
#assert_axioms step_emission
end Minidregg.Kernel.GenericSimplexEmissionSupport
