import Kernel.GeneralSimplexReachability
import Kernel.GenericSimplexLocal
import Mathlib.Data.List.Infix

namespace Minidregg.Kernel.GenericSimplexAuditProjection
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexLocal
open Minidregg.Kernel.GeneralSimplexReachability
set_option autoImplicit false

abbrev Event := Minidregg.Kernel.GenericSimplex.AuditEvent

def project (party : Nat) (events : List Event) : List Event :=
  events.filter (fun event => eventOwner event == some party)

@[simp] theorem project_append (party : Nat) (a b : List Event) :
    project party (a ++ b) = project party a ++ project party b := by
  simp [project]

theorem project_owned (party : Nat) (events : List Event)
    (owned : ∀ event ∈ events, eventOwner event = some party) :
    project party events = events := by
  apply List.filter_eq_self.mpr
  intro event member
  simp [owned event member]

theorem project_other (party owner : Nat) (events : List Event)
    (different : party ≠ owner)
    (owned : ∀ event ∈ events, eventOwner event = some owner) :
    project party events = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro event member
  simp [owned event member, Ne.symm different]

theorem project_flatMap_absent (party : Nat) (actors : List Nat)
    (history : Nat → List Event) (absent : party ∉ actors)
    (owned : ∀ actor ∈ actors, ∀ event ∈ history actor, eventOwner event = some actor) :
    project party (actors.flatMap history) = [] := by
  revert absent owned
  induction actors with
  | nil => intro _ _; rfl
  | cons actor rest ih =>
    intro absent owned
    have diff : party ≠ actor := by intro eq; subst party; simp at absent
    have restAbsent : party ∉ rest := by intro mem; exact absent (by simp [mem])
    have head := project_other party actor (history actor) diff (owned actor (by simp))
    have tail := ih restAbsent (fun p hp => owned p (by simp [hp]))
    simpa only [List.flatMap_cons, project_append, head, tail, List.nil_append]

theorem project_flatMap_member (party : Nat) (actors : List Nat)
    (history : Nat → List Event) (unique : actors.Nodup) (member : party ∈ actors)
    (owned : ∀ actor ∈ actors, ∀ event ∈ history actor, eventOwner event = some actor) :
    project party (actors.flatMap history) = history party := by
  revert unique member owned
  induction actors with
  | nil => intro _ member _; simp at member
  | cons actor rest ih =>
    intro unique member owned
    obtain ⟨notAgain, restUnique⟩ := List.nodup_cons.mp unique
    by_cases same : party = actor
    · subst party
      have head := project_owned actor (history actor) (owned actor (by simp))
      have tail := project_flatMap_absent actor rest history notAgain
        (fun p hp => owned p (by simp [hp]))
      simpa only [List.flatMap_cons, project_append, head, tail, List.append_nil]
    · have restMember : party ∈ rest := by simpa [same] using member
      have head := project_other party actor (history actor) same (owned actor (by simp))
      have tail := ih restUnique restMember (fun p hp => owned p (by simp [hp]))
      simpa only [List.flatMap_cons, project_append, head, tail, List.nil_append]

/-- Purely structural local extraction targets. These do not assume agreement,
quorum support, or any form of safety. The executable local proof must construct
this record; no default instance supplies it. -/
structure StructuralAuditLaws (c : Config) : Prop where
  startSelf : ∀ party time, (start c party time).self = party
  startOwned : ∀ party time, OwnedAudit (start c party time)
  stepExtension : ∀ state input, AuditExtension state (step c state input)
  stepOwned : ∀ state input, OwnedAudit state → OwnedAudit (step c state input)

structure ProjectedNetwork (c : Config) (faulty : Finset Nat) (net : Network) : Prop where
  identity : ∀ party, party < c.parties → party ∉ faulty →
    (net.localState party).self = party
  owned : ∀ party, party < c.parties → party ∉ faulty → OwnedAudit (net.localState party)
  projection : ∀ party, party < c.parties → party ∉ faulty →
    project party net.audit = (net.localState party).audit

theorem initial_projected (c : Config) (faulty : Finset Nat) (time : Nat)
    (laws : StructuralAuditLaws c) : ProjectedNetwork c faulty (initial c time) := by
  refine ⟨?_, ?_, ?_⟩
  · intro party _ _; exact laws.startSelf party time
  · intro party _ _; exact laws.startOwned party time
  · intro party member _
    apply project_flatMap_member party (List.range c.parties)
      (fun p => (start c p time).audit) List.nodup_range (by simpa using member)
    intro actor _ event eventMember
    simpa only [laws.startSelf] using laws.startOwned actor time event eventMember

theorem byzantine_audit_projects_empty (faulty : Finset Nat) (input : Input)
    (party : Nat) (honest : party ∉ faulty) :
    project party (byzantineInputAudit faulty input) = [] := by
  cases input with
  | delivery message | deliveryAt time message =>
    by_cases bad : message.sender ∈ faulty
    · have different : party ≠ message.sender := by
        intro same; subst party; exact honest bad
      simp [byzantineInputAudit, bad, project, eventOwner, Ne.symm different]
    · simp [byzantineInputAudit, bad, project]
  | tick time | checked block | offer payload | poll => rfl

theorem advance_projected {c : Config} {faulty : Finset Nat}
    {sourceChecked : Network → Nat → Block → Prop} {net : Network}
    (laws : StructuralAuditLaws c) (prior : ProjectedNetwork c faulty net)
    (party : Nat) (input : Input)
    (allowed : AllowedInput c faulty sourceChecked net party input) :
    ProjectedNetwork c faulty (advance c faulty net party input) := by
  have member := allowed.1
  have honest := allowed.2.1
  have extension := laws.stepExtension (net.localState party) input
  have nextOwned := laws.stepOwned (net.localState party) input (prior.owned party member honest)
  have nextSelf : (step c (net.localState party) input).self = party :=
    extension.sameSelf.trans (prior.identity party member honest)
  have deltaOwned : ∀ event ∈ (step c (net.localState party) input).audit.drop
      (net.localState party).audit.length, eventOwner event = some party := by
    intro event inside
    simpa only [nextSelf] using nextOwned event (List.mem_of_mem_drop inside)
  refine ⟨?_, ?_, ?_⟩
  · intro other otherMember otherHonest
    by_cases same : other = party
    · subst other; simpa only [advance, if_pos rfl] using nextSelf
    · simpa only [advance, if_neg same] using prior.identity other otherMember otherHonest
  · intro other otherMember otherHonest
    by_cases same : other = party
    · subst other; simpa only [advance, if_pos rfl] using nextOwned
    · simpa only [advance, if_neg same] using prior.owned other otherMember otherHonest
  · intro other otherMember otherHonest
    have erased := byzantine_audit_projects_empty faulty input other otherHonest
    have projected := prior.projection other otherMember otherHonest
    by_cases same : other = party
    · subst other
      have kept := project_owned party _ deltaOwned
      simpa only [advance, project_append, erased, projected, kept,
        List.append_nil, if_pos rfl] using (List.prefix_append_drop extension.history).symm
    · have erasedDelta := project_other other party _ same deltaOwned
      simp only [advance, project_append, erased, projected, erasedDelta,
        List.append_nil, if_neg same]

/-- Actual executable start/step reachability supplies the global projection once
local structural preservation is proved. This is not yet LocalFaithful. -/
theorem reachable_projected {c : Config} {faulty : Finset Nat}
    {sourceChecked : Network → Nat → Block → Prop} {initialTime : Nat} {net : Network}
    (laws : StructuralAuditLaws c)
    (reachable : Reachable c faulty sourceChecked initialTime net) :
    ProjectedNetwork c faulty net := by
  induction reachable with
  | initial => exact initial_projected c faulty initialTime laws
  | next prior party input allowed ih => exact advance_projected laws ih party input allowed

/-- An authenticated honest delivery cannot invent a past send. Its source is
an actual retained engine emission in this exact finite global history. -/
theorem authentic_honest_send_in_audit {c : Config} {faulty : Finset Nat}
    {net : Network} {message : Message} (projection : ProjectedNetwork c faulty net)
    (authentic : authenticDelivery c faulty net message) (honest : message.sender ∉ faulty) :
    (.send message : Event) ∈ net.audit := by
  have localMember := authentic.2.resolve_left honest
  rw [← projection.projection message.sender authentic.1 honest] at localMember
  exact (List.mem_filter.mp localMember).1

/-- The sender witness is strictly before every event emitted by the receiving
step, not merely present somewhere in an unconstrained history. -/
theorem authentic_honest_send_before_step {c : Config} {faulty : Finset Nat}
    {net : Network} {message : Message} (projection : ProjectedNetwork c faulty net)
    (authentic : authenticDelivery c faulty net message) (honest : message.sender ∉ faulty) :
    ∃ time < net.audit.length, auditTrace net time = .send message := by
  obtain ⟨time, atTime⟩ := List.mem_iff_getElem?.mp
    (authentic_honest_send_in_audit projection authentic honest)
  obtain ⟨before, _⟩ := List.getElem?_eq_some_iff.mp atTime
  exact ⟨time, before, by simp [auditTrace, atTime]⟩

theorem auditTrace_advance_prior (c : Config) (faulty : Finset Nat) (net : Network)
    (party : Nat) (input : Input) (time : Nat) (before : time < net.audit.length) :
    auditTrace (advance c faulty net party input) time = auditTrace net time := by
  simp only [auditTrace, advance, List.append_assoc, List.getElem?_append_left before]

#assert_axioms authentic_honest_send_before_step
#assert_axioms auditTrace_advance_prior

#assert_axioms initial_projected
#assert_axioms advance_projected
#assert_axioms reachable_projected
#assert_axioms authentic_honest_send_in_audit
end Minidregg.Kernel.GenericSimplexAuditProjection
