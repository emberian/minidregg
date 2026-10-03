import Kernel.GenericSimplexChronology
import Kernel.GenericSimplexEmissionSupport

namespace Minidregg.Kernel.GenericSimplexGlobalEmission
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexLocal
open Minidregg.Kernel.GenericSimplexVAInvariant
open Minidregg.Kernel.GeneralSimplexReachability
open Minidregg.Kernel.GenericSimplexAuditProjection
open Minidregg.Kernel.GenericSimplexChronology
open Minidregg.Kernel.GenericSimplexEmissionSupport
set_option autoImplicit false
abbrev EmissionEvent := Minidregg.Kernel.GenericSimplex.AuditEvent

/-- Same local emission obligations expressed over the actual global trace.
The threshold remains executable c.quorum until the configuration-size join. -/
def GlobalEventSupported (c : Config) (tr : Trace) (roster : Finset Nat)
    (time : Nat) : EmissionEvent → Prop
  | .send message => match message.kind, message.value with
      | .commit, some block => Support tr roster time message.view .vote (some block) c.quorum
      | .candidate, some block => Support tr roster time message.view .vote (some block) (c.faults + 1)
      | .ready, arg => Support tr roster time message.view .candidate arg c.quorum ∨
          Support tr roster time message.view .ready arg (c.faults + 1)
      | _, _ => True
  | .prepare _ view block => Support tr roster time view .vote (some block) c.quorum ∨
      Support tr roster time view .ready (some block) c.quorum ∨
      Support tr roster time view .commit (some block) c.quorum
  | .disable _ view => Support tr roster time view .ready none c.quorum
  | .commit _ view block => Support tr roster time view .commit (some block) c.quorum
  | .idle => True

def SupportedTrace (c : Config) (faulty : Finset Nat) (net : Network) : Prop :=
  ∀ time event party, net.audit[time]? = some event → eventOwner event = some party →
    party ∉ faulty → GlobalEventSupported c (auditTrace net) (Finset.range c.parties) time event

theorem evidence_transport {external : Message → Prop} {history : List EmissionEvent}
    {tr : Trace} {roster : Finset Nat} {time view threshold : Nat} {kind : Kind} {arg : Argument}
    (support : EvidenceSupport external history roster view kind arg threshold)
    (externalBefore : ∀ message, external message → ∃ before < time, tr before = .send message)
    (historyBefore : ∀ event ∈ history, ∃ before < time, tr before = event) :
    Support tr roster time view kind arg threshold := by
  obtain ⟨voters, enrolled, enough, available⟩ := support
  refine ⟨voters, enrolled, enough, ?_⟩
  intro party member
  rcases available party member with outside | retained
  · exact externalBefore _ outside
  · exact historyBefore _ retained

theorem event_supported_transport {c : Config} {external : Message → Prop}
    {history : List EmissionEvent} {tr : Trace} {roster : Finset Nat} {time : Nat}
    {event : EmissionEvent} (supported : EventSupported c external roster history event)
    (externalBefore : ∀ message, external message → ∃ before < time, tr before = .send message)
    (historyBefore : ∀ prior ∈ history, ∃ before < time, tr before = prior) :
    GlobalEventSupported c tr roster time event := by
  have transfer := fun {v k a n} (h : EvidenceSupport external history roster v k a n) =>
    evidence_transport h externalBefore historyBefore
  cases event with
  | send message =>
    rcases message with ⟨party, view, kind, arg⟩
    cases kind <;> cases arg <;> simp only [EventSupported, GlobalEventSupported] at supported ⊢
    all_goals first
      | exact True.intro
      | exact transfer supported
      | exact supported.imp transfer transfer
  | prepare party view block =>
    exact supported.imp transfer (Or.imp transfer transfer)
  | disable party view => exact transfer supported
  | commit party view block => exact transfer supported
  | idle => trivial

/-- At a specific actual owned global event, use the corresponding EXACT local
prefix. External evidence must already exist before this event; membership in
the final global history alone is not accepted. -/
theorem owned_emission_supported {c : Config} {faulty : Finset Nat} {net : Network}
    {external : Message → Prop} (projected : ProjectedNetwork c faulty net)
    (party time : Nat) (event : EmissionEvent) (enrolled : party < c.parties)
    (honest : party ∉ faulty) (atTime : net.audit[time]? = some event)
    (owner : eventOwner event = some party)
    (justified : EmissionJustified c external (Finset.range c.parties) (net.localState party).audit)
    (externalBefore : ∀ message, external message →
      ∃ before < time, auditTrace net before = .send message) :
    GlobalEventSupported c (auditTrace net) (Finset.range c.parties) time event := by
  obtain ⟨localEvent, localPrefix⟩ :=
    projected_event_prefix projected party time event enrolled honest atTime owner
  obtain ⟨within, atLocal⟩ := List.getElem?_eq_some_iff.mp localEvent
  have cause := justified _ within
  rw [atLocal, localPrefix] at cause
  exact event_supported_transport cause externalBefore (fun prior member => projected_prefix_before member)

/-- Appending actual events preserves every earlier strict send witness. -/
theorem support_extend {before after : Network} {roster : Finset Nat}
    {time view threshold : Nat} {kind : Kind} {arg : Argument}
    (extension : before.audit.IsPrefix after.audit)
    (bounded : time ≤ before.audit.length)
    (support : Support (auditTrace before) roster time view kind arg threshold) :
    Support (auditTrace after) roster time view kind arg threshold := by
  obtain ⟨suffix, eq⟩ := extension
  obtain ⟨voters, members, enough, sent⟩ := support
  refine ⟨voters, members, enough, ?_⟩
  intro party member
  obtain ⟨earlier, earlierBound, output⟩ := sent party member
  refine ⟨earlier, earlierBound, ?_⟩
  have inOld : earlier < before.audit.length := Nat.lt_of_lt_of_le earlierBound bounded
  simpa only [Sent, auditTrace, ← eq, List.getElem?_append_left inOld] using output

#assert_axioms evidence_transport
#assert_axioms event_supported_transport
#assert_axioms owned_emission_supported
#assert_axioms support_extend
end Minidregg.Kernel.GenericSimplexGlobalEmission
