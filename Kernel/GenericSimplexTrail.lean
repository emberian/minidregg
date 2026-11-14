import Kernel.GenericSimplexFresh
import Kernel.GenericSimplexEngineSafety
import Kernel.GenericSimplexSupportExtends

/-! The trail of a run of replicas that keep relative blocks.

A running replica (`GenericSimplexRelative`) holds each block as the payloads above the
chain it has committed, and forgets its audit between inputs. This file gives such a run
the trace the abstract model's safety theorem is about, without changing the replica:

* `liftEvent chain`: a replica's event, with every block read as `chain ++ block`.
* `Good`: what a list of whole-chain events must meet, event by event against the strict
  prefix before it, to be a trace of the model (`good_faithful`: it gives `LocalFaithful`).
* `Ghost`: one correct replica's side of the bargain. `G` is a state of the specification
  whose audit is retained; the replica's own state is `forget G`. Every event of `G`'s audit
  and every message it has received is in the trail, read through `chain`.
* `ghost_step`: one `step` of the specification on `G` appends its new events to the trail,
  and both `Good` and `Ghost` hold again. Each new event meets its obligation from the
  specification's own local lemmas (`step_invariant`, `step_causal`, `step_origin`,
  `step_positive`), applied to `G`. -/
namespace Minidregg.Kernel.GenericSimplexTrail
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexLocal
open Minidregg.Kernel.GenericSimplexCausal
open Minidregg.Kernel.GenericSimplexVAInvariant
open Minidregg.Kernel.GeneralSimplexReachability
open Minidregg.Kernel.GenericSimplexPreparedHistory
open Minidregg.Kernel.GenericSimplexVoteOrigin
open Minidregg.Kernel.GenericSimplexPositive
open Minidregg.Kernel.GenericSimplexOutputHistory
open Minidregg.Kernel.GenericSimplexReceiveProvenance
open Minidregg.Kernel.GenericSimplexReceiveScope
open Minidregg.Kernel.GenericSimplexScopeStructure
open Minidregg.Kernel.GenericSimplexEmissionSupport
open Minidregg.Kernel.GenericSimplexStructure
open Minidregg.Kernel.GenericSimplexChronology
open Minidregg.Kernel.GenericSimplexFresh
set_option autoImplicit false

abbrev Event := Minidregg.Kernel.GenericSimplex.AuditEvent

def liftArgument (chain : Block) (value : Argument) : Argument := value.map (chain ++ ·)

/-- The whole-chain message a relative message denotes at a replica that has committed `chain`. -/
def liftMessage (chain : Block) (m : Message) : Message :=
  ⟨m.sender, m.view, m.kind, liftArgument chain m.value⟩

def liftEvent (chain : Block) : Event → Event
  | .send m => .send (liftMessage chain m)
  | .prepare party view block => .prepare party view (chain ++ block)
  | .disable party view => .disable party view
  | .commit party view block => .commit party view (chain ++ block)
  | .idle => .idle

theorem liftEvent_owner (chain : Block) (event : Event) :
    eventOwner (liftEvent chain event) = eventOwner event := by
  cases event <;> rfl

theorem liftArgument_injective (chain : Block) {a b : Argument}
    (same : liftArgument chain a = liftArgument chain b) : a = b := by
  cases a <;> cases b <;> simp_all [liftArgument]

theorem liftEvent_send {chain : Block} {event : Event} {m : Message}
    (lifted : liftEvent chain event = .send m) :
    ∃ value, event = .send ⟨m.sender, m.view, m.kind, value⟩ ∧ liftArgument chain value = m.value := by
  cases event with
  | send original =>
    simp only [liftEvent, AuditEvent.send.injEq] at lifted
    subst lifted
    exact ⟨original.value, rfl, rfl⟩
  | _ => simp [liftEvent] at lifted

/-! ## A list of events that is a trace of the model -/

/-- The three obligations of one event against the events before it. -/
def EventGood (c : Config) (prior : List Event) (event : Event) : Prop :=
  EventSupported c (fun _ => False) (Finset.range c.parties) prior event ∧
    VoteOriginOn prior event ∧ EventPositive event

structure Good (c : Config) (faulty : Finset Nat) (trail : List Event) : Prop where
  events : ∀ index (within : index < trail.length) (owner : Nat),
    eventOwner trail[index] = some owner → owner ∉ faulty →
      EventGood c (trail.take index) trail[index]
  voteOnce : ∀ p v x y, p ∉ faulty → .send ⟨p, v, .vote, some x⟩ ∈ trail →
    .send ⟨p, v, .vote, some y⟩ ∈ trail → x = y
  lock : ∀ p v x a, p ∉ faulty → .send ⟨p, v, .commit, some x⟩ ∈ trail →
    .send ⟨p, v, .candidate, a⟩ ∈ trail → a = some x

theorem trace_at {trail : List Event} {time : Nat} {event : Event}
    (nonidle : event ≠ .idle) (output : localTrace trail time = event) :
    ∃ within : time < trail.length, trail[time] = event := by
  unfold localTrace at output
  cases found : trail[time]? with
  | none => rw [found] at output; exact absurd output.symm nonidle
  | some value =>
    rw [found, Option.getD_some] at output
    obtain ⟨within, same⟩ := List.getElem?_eq_some_iff.mp found
    exact ⟨within, same.trans output⟩

theorem trace_member {trail : List Event} {time : Nat} {event : Event}
    (nonidle : event ≠ .idle) (output : localTrace trail time = event) : event ∈ trail := by
  obtain ⟨within, same⟩ := trace_at nonidle output
  exact same ▸ List.getElem_mem within

theorem member_before {trail : List Event} {time : Nat} {event : Event}
    (member : event ∈ trail.take time) : ∃ before < time, localTrace trail before = event := by
  obtain ⟨index, within, same⟩ := List.mem_iff_getElem.mp member
  rw [List.length_take] at within
  rw [List.getElem_take] at same
  refine ⟨index, by omega, ?_⟩
  unfold localTrace
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  exact same

theorem evidence_support {trail : List Event} {roster : Finset Nat} {time view threshold : Nat}
    {kind : Kind} {arg : Argument}
    (evidence : EvidenceSupport (fun _ => False) (trail.take time) roster view kind arg threshold) :
    Support (localTrace trail) roster time view kind arg threshold := by
  obtain ⟨voters, members, enough, available⟩ := evidence
  refine ⟨voters, members, enough, fun party member => ?_⟩
  rcases available party member with impossible | sent
  · exact impossible.elim
  · exact member_before sent

/-- **A good list of events is a trace of the abstract model.** -/
theorem good_faithful {c : Config} {faulty : Finset Nat} {trail : List Event}
    (good : Good c faulty trail) (size : c.parties = 3 * c.faults + 1) :
    LocalFaithful (localTrace trail) (Finset.range c.parties) faulty c.faults := by
  have quorum : c.quorum = 2 * c.faults + 1 := by unfold Config.quorum; omega
  have at_ : ∀ {time : Nat} {event : Event} (owner : Nat), event ≠ .idle →
      localTrace trail time = event → eventOwner event = some owner → owner ∉ faulty →
      EventGood c (trail.take time) event := by
    intro time event owner nonidle output owned honest
    obtain ⟨within, same⟩ := trace_at nonidle output
    have result := good.events time within owner (by rw [same]; exact owned) honest
    rwa [same] at result
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t u p v x y honest first second
    exact good.voteOnce p v x y honest (trace_member (by simp) first) (trace_member (by simp) second)
  · intro t p v x honest sent
    have cause := (at_ p (by simp) sent rfl honest).1
    simp only [EventSupported, quorum] at cause
    exact evidence_support cause
  · intro t u p v x a honest first second
    exact good.lock p v x a honest (trace_member (by simp) first) (trace_member (by simp) second)
  · intro t p v x honest sent
    have cause := (at_ p (by simp) sent rfl honest).1
    simp only [EventSupported] at cause
    exact evidence_support cause
  · intro t p v a honest sent
    have cause := (at_ p (by simp) sent rfl honest).1
    simp only [EventSupported, quorum] at cause
    exact cause.imp evidence_support evidence_support
  · intro t p v x honest output
    have cause := (at_ p (by simp) output rfl honest).1
    simp only [EventSupported, quorum] at cause
    exact cause.imp evidence_support (fun rest => rest.imp evidence_support evidence_support)
  · intro t p v honest output
    have cause := (at_ p (by simp) output rfl honest).1
    simp only [EventSupported, quorum] at cause
    exact evidence_support cause
  · intro t p v x honest output
    have cause := (at_ p (by simp) output rfl honest).1
    simp only [EventSupported, quorum] at cause
    exact evidence_support cause
  · intro t p v x honest sent
    have cause := (at_ p (by simp) sent rfl honest).2.1
    simp only [VoteOriginOn] at cause
    rcases cause with safe | prepared
    · left
      exact safeAt_transport (trail.take t) (localTrace trail) t p v x
        (fun event member => member_before member) safe
    · exact Or.inr (member_before prepared)
  · intro t p v x honest output
    exact (at_ p (by simp) output rfl honest).2.2
  · intro t p v x honest output
    exact (at_ p (by simp) output rfl honest).2.2
  · intro t p v honest output
    exact (at_ p (by simp) output rfl honest).2.2

/-- Appending events keeps a list good when each appended event of a correct owner meets
its obligations against everything before it, and the two pairwise rules hold. -/
theorem good_append {c : Config} {faulty : Finset Nat} {trail extra : List Event}
    (good : Good c faulty trail)
    (each : ∀ index (within : index < extra.length) (owner : Nat),
      eventOwner extra[index] = some owner → owner ∉ faulty →
        EventGood c (trail ++ extra.take index) extra[index])
    (voteOnce : ∀ p v x y, p ∉ faulty → .send ⟨p, v, .vote, some x⟩ ∈ trail ++ extra →
      .send ⟨p, v, .vote, some y⟩ ∈ trail ++ extra → x = y)
    (lock : ∀ p v x a, p ∉ faulty → .send ⟨p, v, .commit, some x⟩ ∈ trail ++ extra →
      .send ⟨p, v, .candidate, a⟩ ∈ trail ++ extra → a = some x) :
    Good c faulty (trail ++ extra) := by
  refine ⟨?_, voteOnce, lock⟩
  intro index within owner owned honest
  by_cases old : index < trail.length
  · rw [List.take_append_of_le_length (Nat.le_of_lt old)]
    rw [List.getElem_append_left old] at owned ⊢
    exact good.events index old owner owned honest
  · have later : trail.length ≤ index := Nat.le_of_not_lt old
    rw [List.length_append] at within
    rw [List.take_append, List.take_of_length_le later]
    rw [List.getElem_append_right later] at owned ⊢
    exact each (index - trail.length) (by omega) owner owned honest

/-- Events of faulty members, and idle entries, are free. -/
theorem good_append_free {c : Config} {faulty : Finset Nat} {trail extra : List Event}
    (good : Good c faulty trail)
    (free : ∀ event ∈ extra, ∀ owner, eventOwner event = some owner → owner ∈ faulty) :
    Good c faulty (trail ++ extra) := by
  have old : ∀ {p v kind value}, p ∉ faulty → (.send ⟨p, v, kind, value⟩ : Event) ∈ trail ++ extra →
      (.send ⟨p, v, kind, value⟩ : Event) ∈ trail := by
    intro p v kind value honest member
    rcases List.mem_append.mp member with inside | added
    · exact inside
    · exact absurd (free _ added p rfl) honest
  apply good_append good
  · intro index within owner owned honest
    exact absurd (free _ (List.getElem_mem within) owner owned) honest
  · intro p v x y honest first second
    exact good.voteOnce p v x y honest (old honest first) (old honest second)
  · intro p v x a honest first second
    exact good.lock p v x a honest (old honest first) (old honest second)

theorem trace_extend {trail extra : List Event} {time : Nat} {event : Event}
    (nonidle : event ≠ .idle) (output : localTrace trail time = event) :
    localTrace (trail ++ extra) time = event := by
  obtain ⟨within, same⟩ := trace_at nonidle output
  unfold localTrace
  rw [List.getElem?_append_left within, List.getElem?_eq_getElem within, Option.getD_some]
  exact same

theorem committed_extend {faulty : Finset Nat} {trail extra : List Event} {view : Nat} {block : Block}
    (committed : CommittedAt (localTrace trail) faulty view block) :
    CommittedAt (localTrace (trail ++ extra)) faulty view block := by
  rcases committed with genesis | ⟨time, party, honest, output⟩
  · exact Or.inl genesis
  · exact Or.inr ⟨time, party, honest, trace_extend (by simp) output⟩

theorem committed_of_member {faulty : Finset Nat} {trail : List Event} {party view : Nat} {block : Block}
    (honest : party ∉ faulty) (member : (.commit party view block : Event) ∈ trail) :
    CommittedAt (localTrace trail) faulty view block := by
  obtain ⟨index, within, same⟩ := List.mem_iff_getElem.mp member
  refine Or.inr ⟨index, party, honest, ?_⟩
  unfold localTrace
  rw [List.getElem?_eq_getElem within, Option.getD_some]
  exact same

/-! ## Moving support between a replica's relative events and the trail -/

/-- `SafeAt` on a list, by membership. -/
theorem safeAt_iff (history : List Event) (party view : Nat) (block : Block) :
    SafeAt (localTrace history) history.length party view block ↔
      block ≠ [] ∧ ∃ previous < view,
        ((previous = 0 ∧ block.dropLast = []) ∨ .prepare party previous block.dropLast ∈ history) ∧
        ∀ skipped, previous < skipped → skipped < view → .disable party skipped ∈ history := by
  constructor
  · rintro ⟨nonempty, previous, older, prepared, disabled⟩
    refine ⟨nonempty, previous, older, ?_, ?_⟩
    · rcases prepared with genesis | ⟨before, _, output⟩
      · exact Or.inl genesis
      · exact Or.inr (trace_member (by simp) output)
    · intro skipped low high
      obtain ⟨before, _, output⟩ := disabled skipped low high
      exact trace_member (by simp) output
  · rintro ⟨nonempty, previous, older, prepared, disabled⟩
    refine ⟨nonempty, previous, older, ?_, ?_⟩
    · rcases prepared with genesis | member
      · exact Or.inl genesis
      · exact Or.inr (earlier_from_member history _ member)
    · intro skipped low high
      exact earlier_from_member history _ (disabled skipped low high)

theorem supported_map {c : Config} {roster : Finset Nat} {source target : Message → Prop}
    {before after : List Event} (reads : Event → Event)
    (argument : Argument → Argument)
    (sends : ∀ m : Message, reads (.send m) = .send ⟨m.sender, m.view, m.kind, argument m.value⟩)
    (prepares : ∀ party view block, ∃ image, argument (some block) = some image ∧
      reads (.prepare party view block) = .prepare party view image ∧
      reads (.commit party view block) = .commit party view image)
    (disables : ∀ party view, reads (.disable party view) = .disable party view)
    (bottom : argument none = none) (idles : reads .idle = .idle)
    (move : ∀ view kind arg threshold, EvidenceSupport source before roster view kind arg threshold →
      EvidenceSupport target after roster view kind (argument arg) threshold)
    (event : Event) (supported : EventSupported c source roster before event) :
    EventSupported c target roster after (reads event) := by
  cases event with
  | send message =>
    obtain ⟨sender, view, kind, arg⟩ := message
    rw [sends]
    cases arg with
    | none =>
      show EventSupported c target roster after (.send ⟨sender, view, kind, argument none⟩)
      rw [bottom]
      cases kind <;> simp only [EventSupported] at supported ⊢
      exact supported.imp (fun h => by simpa only [bottom] using move _ _ _ _ h)
        (fun h => by simpa only [bottom] using move _ _ _ _ h)
    | some block =>
      obtain ⟨image, named, _, _⟩ := prepares 0 0 block
      show EventSupported c target roster after (.send ⟨sender, view, kind, argument (some block)⟩)
      rw [named]
      cases kind <;> simp only [EventSupported] at supported ⊢
      all_goals first
        | exact (by simpa only [named] using move _ _ _ _ supported)
        | exact supported.imp (fun h => by simpa only [named] using move _ _ _ _ h)
            (fun h => by simpa only [named] using move _ _ _ _ h)
  | prepare party view block =>
    obtain ⟨image, named, same, _⟩ := prepares party view block
    rw [same]
    simp only [EventSupported] at supported ⊢
    exact supported.imp (fun h => by simpa only [named] using move _ _ _ _ h) (fun rest => rest.imp
      (fun h => by simpa only [named] using move _ _ _ _ h)
      (fun h => by simpa only [named] using move _ _ _ _ h))
  | disable party view =>
    rw [disables]
    simp only [EventSupported] at supported ⊢
    simpa only [bottom] using move _ _ _ _ supported
  | commit party view block =>
    obtain ⟨image, named, _, same⟩ := prepares party view block
    rw [same]
    simp only [EventSupported] at supported ⊢
    simpa only [named] using move _ _ _ _ supported
  | idle => rw [idles]; exact True.intro

/-- The mirror of `supported_map`: support of the image gives support of the event. -/
theorem supported_unmap {c : Config} {roster : Finset Nat} {source target : Message → Prop}
    {before after : List Event} (reads : Event → Event)
    (argument : Argument → Argument)
    (sends : ∀ m : Message, reads (.send m) = .send ⟨m.sender, m.view, m.kind, argument m.value⟩)
    (prepares : ∀ party view block, ∃ image, argument (some block) = some image ∧
      reads (.prepare party view block) = .prepare party view image ∧
      reads (.commit party view block) = .commit party view image)
    (disables : ∀ party view, reads (.disable party view) = .disable party view)
    (bottom : argument none = none)
    (move : ∀ view kind arg threshold,
      EvidenceSupport source before roster view kind (argument arg) threshold →
      EvidenceSupport target after roster view kind arg threshold)
    (event : Event) (supported : EventSupported c source roster before (reads event)) :
    EventSupported c target roster after event := by
  cases event with
  | send message =>
    obtain ⟨sender, view, kind, arg⟩ := message
    rw [sends] at supported
    cases arg with
    | none =>
      replace supported : EventSupported c source roster before
          (.send ⟨sender, view, kind, argument none⟩) := supported
      rw [bottom] at supported
      cases kind <;> simp only [EventSupported] at supported ⊢
      exact supported.imp (fun h => move _ _ none _ (by simpa only [bottom] using h))
        (fun h => move _ _ none _ (by simpa only [bottom] using h))
    | some block =>
      obtain ⟨image, named, _, _⟩ := prepares 0 0 block
      replace supported : EventSupported c source roster before
          (.send ⟨sender, view, kind, argument (some block)⟩) := supported
      rw [named] at supported
      cases kind <;> simp only [EventSupported] at supported ⊢
      all_goals first
        | exact move _ _ (some block) _ (by simpa only [named] using supported)
        | exact supported.imp (fun h => move _ _ (some block) _ (by simpa only [named] using h))
            (fun h => move _ _ (some block) _ (by simpa only [named] using h))
  | prepare party view block =>
    obtain ⟨image, named, same, _⟩ := prepares party view block
    rw [same] at supported
    simp only [EventSupported] at supported ⊢
    exact supported.imp (fun h => move _ _ (some block) _ (by simpa only [named] using h))
      (fun rest => rest.imp
        (fun h => move _ _ (some block) _ (by simpa only [named] using h))
        (fun h => move _ _ (some block) _ (by simpa only [named] using h)))
  | disable party view =>
    rw [disables] at supported
    simp only [EventSupported] at supported ⊢
    exact move _ _ none _ (by simpa only [bottom] using supported)
  | commit party view block =>
    obtain ⟨image, named, _, same⟩ := prepares party view block
    rw [same] at supported
    simp only [EventSupported] at supported ⊢
    exact move _ _ (some block) _ (by simpa only [named] using supported)
  | idle => exact True.intro

theorem member_trace {trail : List Event} {event : Event} (member : event ∈ trail) :
    ∃ time, localTrace trail time = event := by
  obtain ⟨index, within, same⟩ := List.mem_iff_getElem.mp member
  refine ⟨index, ?_⟩
  unfold localTrace
  rw [List.getElem?_eq_getElem within, Option.getD_some]
  exact same

theorem voteOrigin_mono {before after : List Event} (grows : ∀ event ∈ before, event ∈ after)
    (event : Event) (origin : VoteOriginOn before event) : VoteOriginOn after event := by
  cases event with
  | send message =>
    obtain ⟨sender, view, kind, arg⟩ := message
    cases kind <;> cases arg <;> simp only [VoteOriginOn] at origin ⊢
    rename_i block
    rcases origin with safe | prepared
    · left
      obtain ⟨nonempty, previous, older, parent, skipped⟩ := (safeAt_iff _ _ _ _).mp safe
      exact (safeAt_iff _ _ _ _).mpr ⟨nonempty, previous, older, parent.imp id (grows _),
        fun view low high => grows _ (skipped view low high)⟩
    · exact Or.inr (grows _ prepared)
  | _ => exact True.intro

theorem emitted_at {c : Config} {external : Message → Prop} {roster : Finset Nat}
    {old fresh : List Event} (index : Nat) (within : index < fresh.length)
    (emitted : EmissionJustified c external roster (old ++ fresh)) :
    EventSupported c external roster (old ++ fresh.take index) fresh[index] := by
  have at_ := emitted (old.length + index) (by rw [List.length_append]; omega)
  rw [List.take_append, List.take_of_length_le (by omega),
    List.getElem_append_right (by omega)] at at_
  simpa using at_

theorem origins_at {old fresh : List Event} (index : Nat) (within : index < fresh.length)
    (origins : VoteOrigins (old ++ fresh)) :
    VoteOriginOn (old ++ fresh.take index) fresh[index] := by
  have at_ := origins (old.length + index) (by rw [List.length_append]; omega)
  rw [List.take_append, List.take_of_length_le (by omega),
    List.getElem_append_right (by omega)] at at_
  simpa using at_

theorem step_live (c : Config) (s : State) (input : Input) (live : s.lastCommitted < s.current) :
    (step c s input).lastCommitted < (step c s input).current := by
  rw [Minidregg.Kernel.GenericSimplexErasure.step_eq]
  split
  · exact live
  · rename_i alive
    have budget : 0 < c.pumpBudget := by
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, not_or, Bool.not_eq_false] at alive
      have formed := alive.1.1
      simp only [Config.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at formed
      exact formed.2
    exact Minidregg.Kernel.GenericSimplexErasure.pump_above c c.pumpBudget _ (Or.inl budget)

/-! ## One correct replica against the trail -/

/-- `G` is a specification state with its audit retained, read through `chain`; the
replica's own state is `forget G`. `base` is the view in which `chain` was committed.
`embed`, `received`: its events and the messages it holds are in the trail. `complete`: a
VOTE, CANDIDATE or COMMIT of this member in the trail, for a view above its floor, is one
of `G`'s audit. -/
structure Ghost (c : Config) (faulty : Finset Nat) (p base : Nat) (chain : Block)
    (trail : List Event) (G : State) : Prop where
  self : G.self = p
  causal : CausalInvariant G
  history : HistoryInvariant G
  origins : VoteOrigins G.audit
  positive : Positive G
  scope : Scoped c G
  output : OutputHistory G
  owned : OwnedAudit G
  live : G.lastCommitted < G.current
  baseLe : base ≤ G.lastCommitted
  committed : CommittedAt (localTrace trail) faulty base chain
  embed : ∀ event ∈ G.audit, liftEvent chain event ∈ trail
  received : ∀ view ∈ G.views, ∀ m ∈ view.received, (.send (liftMessage chain m) : Event) ∈ trail
  complete : ∀ v kind value, (kind = .vote ∨ kind = .candidate ∨ kind = .commit) →
    G.lastCommitted < v → (.send ⟨p, v, kind, value⟩ : Event) ∈ trail →
      ∃ relative, (.send ⟨p, v, kind, relative⟩ : Event) ∈ G.audit ∧
        liftArgument chain relative = value
  evidenceViews : ∀ m ∈ G.floorEvidence, m.view ≤ G.lastCommitted

/-- Events of other owners leave a replica's side as it was. -/
theorem ghost_extend {c : Config} {faulty : Finset Nat} {p base : Nat} {chain : Block}
    {trail : List Event} {G : State} (extra : List Event)
    (ghost : Ghost c faulty p base chain trail G)
    (others : ∀ m, (.send m : Event) ∈ extra → m.sender ≠ p) :
    Ghost c faulty p base chain (trail ++ extra) G :=
  { ghost with
    committed := committed_extend ghost.committed
    embed := fun event member => List.mem_append.mpr (Or.inl (ghost.embed event member))
    received := fun view stored m member =>
      List.mem_append.mpr (Or.inl (ghost.received view stored m member))
    complete := fun v kind value kindOK above member => by
      rcases List.mem_append.mp member with inside | added
      · exact ghost.complete v kind value kindOK above inside
      · exact absurd rfl (others _ added) }

/-- **One step of a correct replica.** The specification's `step` on `G` appends `fresh`
to its audit; read through `chain` and appended to the trail, those events keep the trail
good, and the replica's side holds for the new state. The last three clauses are what the
durable record needs: every new event is this member's, every new SEND is in the outbox
(or was in the trail already), and every outbox message is an old one or a SEND of the
trail. -/
theorem ghost_step {c : Config} {faulty : Finset Nat} {p base : Nat} {chain : Block}
    {trail : List Event} {G : State} (input : Input)
    (ghost : Ghost c faulty p base chain trail G) (good : Good c faulty trail)
    (honest : p ∉ faulty) (size : c.parties = 3 * c.faults + 1) (faultBound : faulty.card ≤ c.faults)
    (available : InputAvailable (fun m => (.send (liftMessage chain m) : Event) ∈ trail) input) :
    ∃ fresh : List Event, (step c G input).audit = G.audit ++ fresh ∧
      Ghost c faulty p base chain (trail ++ fresh.map (liftEvent chain)) (step c G input) ∧
      Good c faulty (trail ++ fresh.map (liftEvent chain)) ∧
      (∀ event ∈ fresh, eventOwner event = some p) ∧
      (∀ m, (.send m : Event) ∈ fresh →
        m ∈ (step c G input).outbox ∨ (.send (liftMessage chain m) : Event) ∈ trail) ∧
      (∀ m ∈ (step c G input).outbox, m ∈ G.outbox ∨
        (.send (liftMessage chain m) : Event) ∈ trail ++ fresh.map (liftEvent chain)) := by
  obtain ⟨⟨sameSelf, ⟨fresh, audit⟩⟩, ownedStep⟩ := step_preserves c G input
  refine ⟨fresh, audit.symm, ?_⟩
  have rules := good_faithful good size
  have roster : (Finset.range c.parties).card = 3 * c.faults + 1 := by simpa using size
  have self1 : (step c G input).self = p := sameSelf.trans ghost.self
  have backed : Backed (fun m => (.send (liftMessage chain m) : Event) ∈ trail) G :=
    fun view stored m received => Or.inl (ghost.received view stored m received)
  have ownerOf : ∀ event ∈ G.audit, eventOwner event = some p := fun event member =>
    (ghost.owned event member).trans (congrArg some ghost.self)
  have oldEmission : EmissionJustified c (fun m => (.send (liftMessage chain m) : Event) ∈ trail)
      (Finset.range c.parties) G.audit := by
    intro index within
    obtain ⟨t, tw, same⟩ := List.mem_iff_getElem.mp (ghost.embed _ (List.getElem_mem within))
    have cause := (good.events t tw p
      (by rw [same, liftEvent_owner]; exact ownerOf _ (List.getElem_mem within)) honest).1
    rw [same] at cause
    refine supported_unmap (liftEvent chain) (liftArgument chain) (fun m => rfl)
      (fun party view block => ⟨chain ++ block, rfl, rfl, rfl⟩) (fun _ _ => rfl) rfl ?_ _ cause
    rintro view kind arg threshold ⟨voters, members, enough, sent⟩
    refine ⟨voters, members, enough, fun party member => ?_⟩
    rcases sent party member with impossible | inside
    · exact impossible.elim
    · exact Or.inl (List.mem_of_mem_take inside)
  have emission := step_invariant c _ G input size ⟨ghost.scope, backed, oldEmission⟩ available
  have causal1 := step_causal c G input ghost.causal
  have origin1 := step_origin c G input ⟨ghost.history, ghost.origins⟩
  have positive1 := step_positive c G input ghost.positive
  have owned1 := ownedStep ghost.owned
  obtain ⟨floorLe, freshAudit, freshOutbox⟩ := step_fresh c G input ghost.causal ghost.live
  have inNew : ∀ event ∈ fresh, event ∈ (step c G input).audit := fun event member => by
    rw [← audit]; exact List.mem_append.mpr (Or.inr member)
  have inOld : ∀ event ∈ G.audit, event ∈ (step c G input).audit := fun event member => by
    rw [← audit]; exact List.mem_append.mpr (Or.inl member)
  have owner1 : ∀ event ∈ (step c G input).audit, eventOwner event = some p := fun event member =>
    (owned1 event member).trans (congrArg some self1)
  have embed1 : ∀ event ∈ (step c G input).audit,
      liftEvent chain event ∈ trail ++ fresh.map (liftEvent chain) := by
    intro event member
    rw [← audit] at member
    rcases List.mem_append.mp member with old | new
    · exact List.mem_append.mpr (Or.inl (ghost.embed event old))
    · exact List.mem_append.mpr (Or.inr (List.mem_map_of_mem new))
  have classify : ∀ event ∈ fresh, liftEvent chain event ∈ trail ∨
      (EventAbove G.lastCommitted event ∧ ∀ m, event = .send m → m ∈ (step c G input).outbox) :=
    fun event member => (freshAudit event (inNew event member)).imp (ghost.embed event) id
  have located : ∀ v kind value, (kind = .vote ∨ kind = .candidate ∨ kind = .commit) →
      G.lastCommitted < v → (.send ⟨p, v, kind, value⟩ : Event) ∈ trail ++ fresh.map (liftEvent chain) →
      ∃ relative, (.send ⟨p, v, kind, relative⟩ : Event) ∈ (step c G input).audit ∧
        liftArgument chain relative = value := by
    intro v kind value kindOK above member
    rcases List.mem_append.mp member with inside | added
    · obtain ⟨relative, stored, same⟩ := ghost.complete v kind value kindOK above inside
      exact ⟨relative, inOld _ stored, same⟩
    · obtain ⟨event, isNew, lifted⟩ := List.mem_map.mp added
      obtain ⟨relative, named, same⟩ := liftEvent_send lifted
      exact ⟨relative, named ▸ inNew event isNew, same⟩
  have aboveNew : ∀ q v kind value, (.send ⟨q, v, kind, value⟩ : Event) ∈ trail ++ fresh.map (liftEvent chain) →
      (.send ⟨q, v, kind, value⟩ : Event) ∈ trail ∨ (q = p ∧ G.lastCommitted < v) := by
    intro q v kind value member
    rcases List.mem_append.mp member with inside | added
    · exact Or.inl inside
    · obtain ⟨event, isNew, lifted⟩ := List.mem_map.mp added
      rcases classify event isNew with old | ⟨above, _⟩
      · exact Or.inl (lifted ▸ old)
      · obtain ⟨relative, named, _⟩ := liftEvent_send lifted
        subst named
        have owner := owner1 _ (inNew _ isNew)
        simp only [eventOwner, Option.some.injEq] at owner
        exact Or.inr ⟨owner, above⟩
  have someOf : ∀ {relative : Argument} {x : Block}, liftArgument chain relative = some x →
      ∃ y, relative = some y ∧ chain ++ y = x := by
    intro relative x same
    cases relative with
    | none => simp [liftArgument] at same
    | some y => exact ⟨y, rfl, by simpa [liftArgument] using same⟩
  have good1 : Good c faulty (trail ++ fresh.map (liftEvent chain)) := by
    apply good_append good
    · intro index within owner owned honestOwner
      rw [List.length_map] at within
      rw [List.getElem_map] at owned ⊢
      rw [← List.map_take]
      have member : fresh[index] ∈ fresh := List.getElem_mem within
      have lifts : ∀ event ∈ G.audit ++ fresh.take index,
          liftEvent chain event ∈ trail ++ (fresh.take index).map (liftEvent chain) := by
        intro event inside
        rcases List.mem_append.mp inside with old | new
        · exact List.mem_append.mpr (Or.inl (ghost.embed event old))
        · exact List.mem_append.mpr (Or.inr (List.mem_map_of_mem new))
      refine ⟨?_, ?_, ?_⟩
      · have emitted : EmissionJustified c (fun m => (.send (liftMessage chain m) : Event) ∈ trail)
            (Finset.range c.parties) (G.audit ++ fresh) := by rw [audit]; exact emission.emitted
        refine supported_map (liftEvent chain) (liftArgument chain) (fun m => rfl)
          (fun party view block => ⟨chain ++ block, rfl, rfl, rfl⟩) (fun _ _ => rfl) rfl rfl ?_ _
          (emitted_at index within emitted)
        rintro view kind arg threshold ⟨voters, members, enough, sent⟩
        refine ⟨voters, members, enough, fun party voter => Or.inr ?_⟩
        rcases sent party voter with external | inside
        · exact List.mem_append.mpr (Or.inl external)
        · exact lifts _ inside
      · rcases classify _ member with old | ⟨above, _⟩
        · obtain ⟨t, tw, same⟩ := List.mem_iff_getElem.mp old
          have cause := (good.events t tw owner (by rw [same]; exact owned) honestOwner).2.1
          rw [same] at cause
          exact voteOrigin_mono (fun event inside =>
            List.mem_append.mpr (Or.inl (List.mem_of_mem_take inside))) _ cause
        · have origins : VoteOrigins (G.audit ++ fresh) := by rw [audit]; exact origin1.2
          have cause := origins_at index within origins
          have owner := owner1 _ (inNew _ member)
          generalize fresh[index] = event at cause above owner ⊢
          cases event with
          | send message =>
            obtain ⟨sender, view, kind, arg⟩ := message
            cases kind <;> cases arg <;>
              simp only [VoteOriginOn, liftEvent, liftMessage, liftArgument, Option.map] at cause ⊢
            rename_i block
            simp only [eventOwner, Option.some.injEq] at owner
            subst owner
            rcases cause with safe | prepared
            · left
              obtain ⟨nonempty, previous, older, parent, skipped⟩ := (safeAt_iff _ _ _ _).mp safe
              have last : (chain ++ block).dropLast = chain ++ block.dropLast :=
                List.dropLast_append_of_ne_nil nonempty
              have disabled : ∀ view, previous < view → view < _ →
                  (.disable sender view : Event) ∈ trail ++ (fresh.take index).map (liftEvent chain) :=
                fun view low high => lifts _ (skipped view low high)
              refine (safeAt_iff _ _ _ _).mpr ⟨by simp [nonempty], previous, older, ?_, disabled⟩
              rw [last]
              rcases parent with ⟨zero, empty⟩ | stored
              · left
                refine ⟨zero, ?_⟩
                have genesis : chain = [] := by
                  by_cases origin : base = 0
                  · exact known_zero rules (committed_known (origin ▸ ghost.committed))
                  · exfalso
                    have skippedBase := skipped base (by omega) (by have := ghost.baseLe; exact Nat.lt_of_le_of_lt this above)
                    have inTrail : (.disable sender base : Event) ∈ trail := by
                      rcases List.mem_append.mp skippedBase with old | new
                      · exact ghost.embed _ old
                      · rcases classify _ (List.mem_of_mem_take new) with old | ⟨higher, _⟩
                        · exact old
                        · have : G.lastCommitted < base := higher
                          have := ghost.baseLe
                          omega
                    obtain ⟨time, output⟩ := member_trace inTrail
                    exact committed_not_disabled rules roster faultBound ghost.committed honest output
                rw [genesis, empty]
                rfl
              · exact Or.inr (lifts _ stored)
            · exact Or.inr (lifts _ prepared)
          | _ => exact True.intro
      · have pos := positive1.2.2 _ (inNew _ member)
        generalize fresh[index] = event at pos ⊢
        cases event <;> exact pos
    · intro q v x y honestOwner first second
      rcases aboveNew q v .vote (some x) first with oldFirst | ⟨rfl, above⟩
      · rcases aboveNew q v .vote (some y) second with oldSecond | ⟨rfl, above⟩
        · exact good.voteOnce q v x y honestOwner oldFirst oldSecond
        · obtain ⟨a, sa, la⟩ := located v .vote (some x) (Or.inl rfl) above first
          obtain ⟨b, sb, lb⟩ := located v .vote (some y) (Or.inl rfl) above second
          obtain ⟨x0, rfl, rfl⟩ := someOf la
          obtain ⟨y0, rfl, rfl⟩ := someOf lb
          rw [← self1] at sa sb
          rw [causal1.voteOnce v x0 y0 sa sb]
      · obtain ⟨a, sa, la⟩ := located v .vote (some x) (Or.inl rfl) above first
        obtain ⟨b, sb, lb⟩ := located v .vote (some y) (Or.inl rfl) above second
        obtain ⟨x0, rfl, rfl⟩ := someOf la
        obtain ⟨y0, rfl, rfl⟩ := someOf lb
        rw [← self1] at sa sb
        rw [causal1.voteOnce v x0 y0 sa sb]
    · intro q v x a honestOwner first second
      have both : G.lastCommitted < v → q = p → a = some x := by
        intro above named
        subst named
        obtain ⟨rc, sc, lc⟩ := located v .commit (some x) (Or.inr (Or.inr rfl)) above first
        obtain ⟨ra, sa, la⟩ := located v .candidate a (Or.inr (Or.inl rfl)) above second
        obtain ⟨x0, rfl, rfl⟩ := someOf lc
        rw [← self1] at sc sa
        have same := recorded_commit_candidate _ causal1.commitLock causal1.commitRecorded
          causal1.candidateRecorded v x0 ra sc sa
        rw [← la, same]
        rfl
      rcases aboveNew q v .commit (some x) first with oldFirst | ⟨named, above⟩
      · rcases aboveNew q v .candidate a second with oldSecond | ⟨named, above⟩
        · exact good.lock q v x a honestOwner oldFirst oldSecond
        · exact both above named
      · exact both above named
  refine ⟨?_, good1, fun event member => owner1 event (inNew event member), ?_, ?_⟩
  · exact
      { self := self1
        causal := causal1
        history := origin1.1
        origins := origin1.2
        positive := positive1
        scope := emission.scopeOK
        output := step_output c G input ghost.output
        owned := owned1
        live := step_live c G input ghost.live
        baseLe := Nat.le_trans ghost.baseLe floorLe
        committed := committed_extend ghost.committed
        embed := embed1
        received := fun view stored m member => by
          rcases emission.backed view stored m member with external | sent
          · exact List.mem_append.mpr (Or.inl external)
          · exact embed1 _ sent
        complete := fun v kind value kindOK above member =>
          located v kind value kindOK (Nat.lt_of_le_of_lt floorLe above) member
        evidenceViews := fun m member => by
          rcases step_evident c G input with ⟨sameFloor, sameEvidence⟩ | ⟨_, inside⟩
          · rw [sameFloor]
            exact ghost.evidenceViews m (sameEvidence ▸ member)
          · exact Nat.le_of_eq (viewAt_scoped emission.scopeOK _ m (inside m member)).2 }
  · intro m member
    rcases classify _ member with old | ⟨_, sent⟩
    · exact Or.inr old
    · exact Or.inl (sent m rfl)
  · intro m member
    exact (freshOutbox m member).imp id (fun sent => embed1 (.send m) sent)

#assert_axioms good_faithful
#assert_axioms ghost_step

end Minidregg.Kernel.GenericSimplexTrail
