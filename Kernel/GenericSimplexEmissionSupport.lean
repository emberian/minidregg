import Kernel.GenericSimplexCountSupport
import Kernel.GenericSimplexReceiveProvenance
import Kernel.GenericSimplexReceiveScope

namespace Minidregg.Kernel.GenericSimplexEmissionSupport
open Minidregg.Kernel.GenericSimplex
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
    (roster : Finset Nat) (prefix : List AuditEvent) : AuditEvent → Prop
  | .send message => match message.kind, message.value with
      | .commit, some block => EvidenceSupport external prefix roster message.view .vote (some block) c.quorum
      | .candidate, some block => EvidenceSupport external prefix roster message.view .vote (some block) (c.faults + 1)
      | .ready, arg => EvidenceSupport external prefix roster message.view .candidate arg c.quorum ∨
          EvidenceSupport external prefix roster message.view .ready arg (c.faults + 1)
      | _, _ => True
  | .prepare _ view block => EvidenceSupport external prefix roster view .vote (some block) c.quorum ∨
      EvidenceSupport external prefix roster view .ready (some block) c.quorum ∨
      EvidenceSupport external prefix roster view .commit (some block) c.quorum
  | .disable _ view => EvidenceSupport external prefix roster view .ready none c.quorum
  | .commit _ view block => EvidenceSupport external prefix roster view .commit (some block) c.quorum
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
    (prefix : before <+: after) : EvidenceSupport external after roster view kind arg threshold := by
  obtain ⟨voters, members, enough, available⟩ := support
  exact ⟨voters, members, enough, fun party member =>
    (available party member).imp id (fun sent => prefix.sublist.subset sent)⟩

#assert_axioms actual_count_evidence
#assert_axioms evidence_weaken
#assert_axioms evidence_prefix
end Minidregg.Kernel.GenericSimplexEmissionSupport
