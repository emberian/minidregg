import Kernel.GenericSimplexGlobalEmission
import Kernel.GenericSimplexGlobalCausal

namespace Minidregg.Kernel.GenericSimplexNetworkEmission
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexLocal
open Minidregg.Kernel.GenericSimplexVAInvariant
open Minidregg.Kernel.GeneralSimplexReachability
open Minidregg.Kernel.GenericSimplexAuditProjection
open Minidregg.Kernel.GenericSimplexStructure
open Minidregg.Kernel.GenericSimplexGlobalCausal
open Minidregg.Kernel.GenericSimplexEmissionSupport
open Minidregg.Kernel.GenericSimplexGlobalEmission
set_option autoImplicit false
abbrev NetworkEvent := Minidregg.Kernel.GenericSimplex.AuditEvent

def ExternalAt (events : List NetworkEvent) (message : Message) : Prop := .send message ∈ events

def NetworkJustified (c : Config) (faulty : Finset Nat) (net : Network) : Prop :=
  ∀ party, party < c.parties → party ∉ faulty →
    EmissionJustified c (ExternalAt net.audit) (Finset.range c.parties) (net.localState party).audit

theorem event_supported_extend {c : Config} {before after : Network} {roster : Finset Nat}
    {time : Nat} {event : NetworkEvent} (extension : before.audit.IsPrefix after.audit)
    (bounded : time ≤ before.audit.length)
    (supported : GlobalEventSupported c (auditTrace before) roster time event) :
    GlobalEventSupported c (auditTrace after) roster time event := by
  have transfer := fun {v k a n} (h : Support (auditTrace before) roster time v k a n) =>
    support_extend extension bounded h
  cases event with
  | send message =>
    rcases message with ⟨party, view, kind, arg⟩
    cases kind <;> cases arg <;> simp only [GlobalEventSupported] at supported ⊢
    all_goals first | trivial | exact transfer supported | exact supported.imp transfer transfer
  | prepare party view block => exact supported.imp transfer (Or.imp transfer transfer)
  | disable party view => exact transfer supported
  | commit party view block => exact transfer supported
  | idle => trivial

theorem initial_supported_from_local (c : Config) (faulty : Finset Nat) (time : Nat)
    (localJustified : ∀ party, EmissionJustified c (fun _ => False)
      (Finset.range c.parties) (start c party time).audit) :
    SupportedTrace c faulty (initial c time) := by
  intro index event party atTime owner honest
  have member := List.mem_iff_getElem?.mpr ⟨index, atTime⟩
  obtain ⟨sender, enrolled, ownership⟩ := initial_enrolled c time event member
  have same : sender = party := by rw [owner] at ownership; exact (Option.some.inj ownership).symm
  subst sender
  exact owned_emission_supported (initial_projected c faulty time (structuralAuditLaws c))
    party index event enrolled honest atTime owner (localJustified party)
    (fun _ impossible => False.elim impossible)

theorem injected_honest_impossible (faulty : Finset Nat) (input : Input)
    (event : NetworkEvent) (party : Nat) (member : event ∈ byzantineInputAudit faulty input)
    (owner : eventOwner event = some party) (honest : party ∉ faulty) : False := by
  cases input with
  | delivery message | deliveryAt now message =>
    by_cases bad : message.sender ∈ faulty
    · have same : event = .send message := by simpa [byzantineInputAudit, bad] using member
      subst event
      have identity : message.sender = party := by simpa [eventOwner] using owner
      exact honest (identity ▸ bad)
    · simp [byzantineInputAudit, bad] at member
  | tick now | checked block | offer payload | poll => simp [byzantineInputAudit] at member

/-- The next step's external witnesses are bounded by the old global prefix plus
its authenticated Byzantine arrival. Old events use induction; only new local
emissions consume the new local justification. -/
theorem advance_supported_from_local {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {initialTime : Nat} {net : Network}
    (reachable : Reachable c faulty checked initialTime net) (old : SupportedTrace c faulty net)
    (party : Nat) (input : Input) (allowed : AllowedInput c faulty checked net party input)
    (localJustified : EmissionJustified c
      (ExternalAt (net.audit ++ byzantineInputAudit faulty input)) (Finset.range c.parties)
      (step c (net.localState party) input).audit) :
    SupportedTrace c faulty (advance c faulty net party input) := by
  have projected := reachable_projected (structuralAuditLaws c) reachable
  have advancedProjection := advance_projected (structuralAuditLaws c) projected party input allowed
  intro time event actor atTime owner honest
  by_cases inOld : time < net.audit.length
  · have beforeBase : time < (net.audit ++ byzantineInputAudit faulty input).length := by
      simp only [List.length_append]; omega
    have oldAt : net.audit[time]? = some event := by
      simpa only [advance, List.getElem?_append_left beforeBase,
        List.getElem?_append_left inOld] using atTime
    exact event_supported_extend (advance_audit_prefix c faulty net party input)
      (Nat.le_of_lt inOld) (old time event actor oldAt owner honest)
  · have afterOld : net.audit.length ≤ time := by omega
    by_cases inBase : time < (net.audit ++ byzantineInputAudit faulty input).length
    · have injectedAt : (byzantineInputAudit faulty input)[time-net.audit.length]? = some event := by
        simpa only [advance, List.getElem?_append_left inBase,
          List.getElem?_append_right afterOld] using atTime
      exact False.elim (injected_honest_impossible faulty input event actor
        (List.mem_iff_getElem?.mpr ⟨_, injectedAt⟩) owner honest)
    · have afterBase : (net.audit ++ byzantineInputAudit faulty input).length ≤ time := by omega
      have freshAt : ((step c (net.localState party) input).audit.drop
          (net.localState party).audit.length)[time-(net.audit ++ byzantineInputAudit faulty input).length]? = some event := by
        simpa only [advance, List.getElem?_append_right afterBase] using atTime
      have localEntry := List.mem_of_mem_drop (List.mem_iff_getElem?.mpr ⟨_, freshAt⟩)
      have ownership := (structuralAuditLaws c).stepOwned (net.localState party) input
        (projected.owned party allowed.1 allowed.2.1) event localEntry
      have selfSame := ((structuralAuditLaws c).stepExtension (net.localState party) input).sameSelf
      have exactOwner : eventOwner event = some party := by
        simpa only [selfSame, projected.identity party allowed.1 allowed.2.1] using ownership
      have same : actor = party := by rw [owner] at exactOwner; exact Option.some.inj exactOwner
      subst actor
      apply owned_emission_supported advancedProjection party time event allowed.1 honest atTime owner
      · simpa only [advance, if_pos rfl] using localJustified
      · intro message entry
        obtain ⟨before, atBefore⟩ := List.mem_iff_getElem?.mp entry
        obtain ⟨within, _⟩ := List.getElem?_eq_some_iff.mp atBefore
        refine ⟨before, Nat.lt_of_lt_of_le within afterBase, ?_⟩
        simp only [auditTrace, advance, List.getElem?_append_left within, atBefore, Option.getD_some]

theorem initial_network_justified (c : Config) (faulty : Finset Nat) (time : Nat)
    (localJustified : ∀ party, EmissionJustified c (fun _ => False)
      (Finset.range c.parties) (start c party time).audit) :
    NetworkJustified c faulty (initial c time) := by
  intro party enrolled honest
  exact emission_weaken (localJustified party) (fun _ impossible => False.elim impossible)

theorem advance_network_justified {c : Config} {faulty : Finset Nat} {net : Network}
    (old : NetworkJustified c faulty net) (party : Nat) (input : Input)
    (localJustified : EmissionJustified c
      (ExternalAt (net.audit ++ byzantineInputAudit faulty input)) (Finset.range c.parties)
      (step c (net.localState party) input).audit) :
    NetworkJustified c faulty (advance c faulty net party input) := by
  intro other enrolled honest
  by_cases same : other = party
  · subst other
    have widened := emission_weaken localJustified
      (next := ExternalAt (advance c faulty net party input).audit)
      (fun _ entry => List.mem_append.mpr (Or.inl entry))
    simpa only [advance, if_pos rfl] using widened
  · have widened := emission_weaken (old other enrolled honest)
      (next := ExternalAt (advance c faulty net party input).audit)
      (fun _ entry => (advance_audit_prefix c faulty net party input).subset entry)
    simpa only [advance, if_neg same] using widened

#assert_axioms event_supported_extend
#assert_axioms initial_supported_from_local
#assert_axioms advance_supported_from_local
#assert_axioms initial_network_justified
#assert_axioms advance_network_justified
end Minidregg.Kernel.GenericSimplexNetworkEmission
