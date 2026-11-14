import Kernel.GenericSimplexTrail
import Kernel.GenericSimplexRelative

/-! Moving a replica's origin keeps its side of the trail.

After a commit the running replica drops the committed payloads from every block it keeps
(`GenericSimplexRelative.rebase`). `ghost_rebase` is that operation on the proof side: the
replica's specification state with retained audit (`GenericSimplexTrail.Ghost`) is replaced
by one over the longer chain, whose audit is the old one with every event of a view above
the floor read from the new origin (`rebaseEvent`). The floor view keeps only the parent it
offers, the empty block, which now denotes the committed chain.

`Rebased` says what `rebase` did to the views, by view number. That `rebase` meets it is the
caller's to show. The proof uses the abstract model's safety on the trail so far: what a
correct member supports above the committed view strictly extends the commit
(`support_extends_commit`), so nothing of a correct member fails to be read from the new
origin, and a VOTE that is dropped (it leaves a `tombstone`) is a faulty member's. -/
namespace Minidregg.Kernel.GenericSimplexRebaseGhost
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexRelative
open Minidregg.Kernel.GenericSimplexLocal
open Minidregg.Kernel.GenericSimplexCausal
open Minidregg.Kernel.GenericSimplexVAInvariant
open Minidregg.Kernel.GeneralSimplexReachability
open Minidregg.Kernel.GenericSimplexPreparedHistory
open Minidregg.Kernel.GenericSimplexVoteOrigin
open Minidregg.Kernel.GenericSimplexPositive
open Minidregg.Kernel.GenericSimplexOutputHistory
open Minidregg.Kernel.GenericSimplexReceiveScope
open Minidregg.Kernel.GenericSimplexEmissionSupport
open Minidregg.Kernel.GenericSimplexSupportExtends
open Minidregg.Kernel.GenericSimplexTrail
set_option autoImplicit false

theorem mapM_out {α β : Type} (f : α → Option β) : ∀ (items : List α) (out : List β),
    items.mapM f = some out → ∀ y ∈ out, ∃ x ∈ items, f x = some y := by
  intro items
  induction items with
  | nil => intro out same y member; simp at same; subst same; simp at member
  | cons head rest ih =>
    intro out same y member
    rw [List.mapM_cons] at same
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at same
    obtain ⟨image, named, images, restNamed, rfl⟩ := same
    rcases List.mem_cons.mp member with first | later
    · exact ⟨head, by simp, first ▸ named⟩
    · obtain ⟨x, inside, maps⟩ := ih images restNamed y later
      exact ⟨x, by simp [inside], maps⟩

theorem mapM_in {α β : Type} (f : α → Option β) : ∀ (items : List α) (out : List β),
    items.mapM f = some out → ∀ x ∈ items, ∃ y ∈ out, f x = some y := by
  intro items
  induction items with
  | nil => intro out _ x member; simp at member
  | cons head rest ih =>
    intro out same x member
    rw [List.mapM_cons] at same
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at same
    obtain ⟨image, named, images, restNamed, rfl⟩ := same
    rcases List.mem_cons.mp member with first | later
    · exact ⟨image, by simp, first ▸ named⟩
    · obtain ⟨y, inside, maps⟩ := ih images restNamed x later
      exact ⟨y, by simp [inside], maps⟩

/-! ## Reading from the new origin -/

theorem strip_eq {tip block rest : Block} (kept : strip tip block = some rest) :
    block = tip ++ rest ∧ rest ≠ [] := by
  have denotes := strip_denotes [] tip block rest kept
  simp only [List.nil_append] at denotes
  exact ⟨denotes.1.symm, denotes.2⟩

theorem strip_append (tip rest : Block) (nonempty : rest ≠ []) : strip tip (tip ++ rest) = some rest := by
  have positive : 0 < rest.length := List.length_pos_iff.mpr nonempty
  simp [strip, isPrefix, positive]

theorem strip_extends {chain tip block : Block}
    (extends_ : StrictlyExtends (chain ++ tip) (chain ++ block)) : ∃ rest, strip tip block = some rest := by
  obtain ⟨starts, longer⟩ := extends_
  obtain ⟨rest, whole⟩ := starts
  rw [List.append_assoc] at whole
  have same : block = tip ++ rest := (List.append_cancel_left whole).symm
  subst same
  refine ⟨rest, strip_append tip rest ?_⟩
  intro empty
  subst empty
  simp at longer

theorem stripArgument_lift {chain tip : Block} {value kept : Argument}
    (stripped : stripArgument tip value = some kept) :
    liftArgument (chain ++ tip) kept = liftArgument chain value := by
  cases value with
  | none => simp only [stripArgument, Option.some.injEq] at stripped; subst stripped; rfl
  | some block =>
    simp only [stripArgument, Option.map_eq_some_iff] at stripped
    obtain ⟨rest, kept_, rfl⟩ := stripped
    obtain ⟨rfl, _⟩ := strip_eq kept_
    simp [liftArgument, List.append_assoc]

theorem stripOption_some {tip : Block} {value : Option Block} {rest : Block}
    (stripped : stripOption tip value = some (some rest)) :
    ∃ block, value = some block ∧ strip tip block = some rest := by
  cases value with
  | none => simp [stripOption] at stripped
  | some block =>
    simp only [stripOption, Option.map_eq_some_iff, Option.some.injEq] at stripped
    obtain ⟨found, kept, rfl⟩ := stripped
    exact ⟨block, rfl, kept⟩

/-- An event of the old audit, read from the new origin. Events of views at or below the
floor are dropped, except what the floor view still says: its commit (now of the empty
block) and whether it was disabled. -/
def rebaseEvent (floor : Nat) (tip : Block) : Event → Option Event
  | .send m =>
      if floor < m.view then
        (stripArgument tip m.value).map fun value => .send ⟨m.sender, m.view, m.kind, value⟩
      else none
  | .prepare party view block =>
      if floor < view then (strip tip block).map (.prepare party view) else none
  | .disable party view => if floor ≤ view then some (.disable party view) else none
  | .commit party view block =>
      if floor < view then (strip tip block).map (.commit party view)
      else if view = floor ∧ block = tip then some (.commit party view []) else none
  | .idle => none

theorem rebaseEvent_lift {floor : Nat} {chain tip : Block} {event image : Event}
    (read : rebaseEvent floor tip event = some image) :
    liftEvent (chain ++ tip) image = liftEvent chain event := by
  cases event with
  | send m =>
    simp only [rebaseEvent] at read
    split at read
    · simp only [Option.map_eq_some_iff] at read
      obtain ⟨value, stripped, rfl⟩ := read
      simp only [liftEvent, liftMessage, stripArgument_lift stripped]
    · cases read
  | prepare party view block =>
    simp only [rebaseEvent] at read
    split at read
    · simp only [Option.map_eq_some_iff] at read
      obtain ⟨rest, kept, rfl⟩ := read
      obtain ⟨rfl, _⟩ := strip_eq kept
      simp [liftEvent, List.append_assoc]
    · cases read
  | disable party view =>
    simp only [rebaseEvent] at read
    split at read
    · cases read; rfl
    · cases read
  | commit party view block =>
    simp only [rebaseEvent] at read
    split at read
    · simp only [Option.map_eq_some_iff] at read
      obtain ⟨rest, kept, rfl⟩ := read
      obtain ⟨rfl, _⟩ := strip_eq kept
      simp [liftEvent, List.append_assoc]
    · split at read
      · rename_i floorCommit
        cases read
        simp [liftEvent, floorCommit.2]
      · cases read
  | idle => cases read

theorem rebaseEvent_owner {floor : Nat} {tip : Block} {event image : Event}
    (read : rebaseEvent floor tip event = some image) : eventOwner image = eventOwner event := by
  have lifted := congrArg eventOwner (rebaseEvent_lift (chain := []) read)
  rwa [liftEvent_owner, liftEvent_owner] at lifted

theorem rebaseEvent_positive {floor : Nat} {tip : Block} {event image : Event}
    (read : rebaseEvent floor tip event = some image) (positive : EventPositive event) :
    EventPositive image := by
  cases event with
  | send m =>
    simp only [rebaseEvent] at read
    split at read
    · simp only [Option.map_eq_some_iff] at read
      obtain ⟨value, _, rfl⟩ := read
      exact positive
    · cases read
  | prepare party view block =>
    simp only [rebaseEvent] at read
    split at read
    · simp only [Option.map_eq_some_iff] at read
      obtain ⟨rest, _, rfl⟩ := read
      exact positive
    · cases read
  | disable party view =>
    simp only [rebaseEvent] at read
    split at read
    · cases read; exact positive
    · cases read
  | commit party view block =>
    simp only [rebaseEvent] at read
    split at read
    · simp only [Option.map_eq_some_iff] at read
      obtain ⟨rest, _, rfl⟩ := read
      exact positive
    · split at read
      · cases read; exact positive
      · cases read
  | idle => cases read

/-- A SEND of the new audit is a SEND of the old one, for a view above the floor. -/
theorem rebaseEvent_send {floor : Nat} {tip : Block} {event : Event} {m : Message}
    (read : rebaseEvent floor tip event = some (.send m)) :
    ∃ value, event = .send ⟨m.sender, m.view, m.kind, value⟩ ∧ floor < m.view ∧
      stripArgument tip value = some m.value := by
  cases event with
  | send original =>
    simp only [rebaseEvent] at read
    split at read
    · rename_i above
      simp only [Option.map_eq_some_iff, AuditEvent.send.injEq] at read
      obtain ⟨value, stripped, rfl⟩ := read
      exact ⟨original.value, rfl, above, stripped⟩
    · cases read
  | prepare party view block =>
    simp only [rebaseEvent] at read
    split at read
    · simp only [Option.map_eq_some_iff] at read
      obtain ⟨_, _, impossible⟩ := read
      cases impossible
    · cases read
  | disable party view =>
    simp only [rebaseEvent] at read
    split at read <;> cases read
  | commit party view block =>
    simp only [rebaseEvent] at read
    split at read
    · simp only [Option.map_eq_some_iff] at read
      obtain ⟨_, _, impossible⟩ := read
      cases impossible
    · split at read <;> cases read
  | idle => cases read

/-! ## The views after `rebaseView` -/

/-- The received messages `rebaseView` keeps. -/
def keptReceived (tip : Block) (received : List Message) : List Message :=
  received.foldl (fun kept m =>
    match stripArgument tip m.value with
    | some value => kept ++ [{ m with value }]
    | none => if m.kind == .vote then addUnique kept (tombstone m) else kept) []

theorem kept_cases (tip : Block) : ∀ (received kept : List Message) (image : Message),
    image ∈ received.foldl (fun kept m =>
      match stripArgument tip m.value with
      | some value => kept ++ [{ m with value }]
      | none => if m.kind == .vote then addUnique kept (tombstone m) else kept) kept →
    image ∈ kept ∨
      (∃ m ∈ received, stripArgument tip m.value = some image.value ∧
        image = ⟨m.sender, m.view, m.kind, image.value⟩) ∨
      (∃ m ∈ received, stripArgument tip m.value = none ∧ m.kind = .vote ∧ image = tombstone m) := by
  intro received
  induction received with
  | nil => intro kept image member; exact Or.inl member
  | cons head rest ih =>
    intro kept image member
    rw [List.foldl_cons] at member
    rcases ih _ image member with inside | ⟨m, stored, stripped, named⟩ | ⟨m, stored, dropped, vote, named⟩
    · split at inside
      · rename_i value stripped
        rcases List.mem_append.mp inside with old | new
        · exact Or.inl old
        · have same : image = { head with value } := by simpa using new
          subst same
          exact Or.inr (Or.inl ⟨head, by simp, stripped, rfl⟩)
      · rename_i dropped
        split at inside
        · rename_i vote
          rcases Minidregg.Kernel.GenericSimplexReceiveProvenance.addUnique_mem _ _ _ inside with old | new
          · exact Or.inl old
          · exact Or.inr (Or.inr ⟨head, by simp, dropped, beq_iff_eq.mp vote, new⟩)
        · exact Or.inl inside
    · exact Or.inr (Or.inl ⟨m, by simp [stored], stripped, named⟩)
    · exact Or.inr (Or.inr ⟨m, by simp [stored], dropped, vote, named⟩)

theorem rebaseView_fields {c : Config} {self : Nat} {tip : Block} {v rv : View}
    (same : rebaseView c self tip v = some rv) :
    rv.number = v.number ∧ rv.voted = v.voted ∧ rv.disabled = v.disabled ∧
      stripOption tip v.sentCommit = some rv.sentCommit ∧
      stripOption tip v.committed = some rv.committed ∧
      v.sentCandidates.mapM (stripArgument tip) = some rv.sentCandidates ∧
      v.prepared.mapM (strip tip) = some rv.prepared ∧
      rv.received = keptReceived tip v.received := by
  unfold rebaseView at same
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at same
  obtain ⟨a, h1, a1, h2, a2, h3, a3, _, a4, _, a5, h6, rest⟩ := same
  repeat' split at rest
  all_goals first
    | (simp only [Option.bind_some, Option.some.injEq] at rest
       subst rest
       exact ⟨rfl, rfl, rfl, h1, h2, h3, h6, rfl⟩)
    | simp at rest

theorem keptReceived_cases {tip : Block} {received : List Message} {image : Message}
    (member : image ∈ keptReceived tip received) :
    (∃ m ∈ received, stripArgument tip m.value = some image.value ∧
      image = ⟨m.sender, m.view, m.kind, image.value⟩) ∨
    (∃ m ∈ received, stripArgument tip m.value = none ∧ m.kind = .vote ∧ image = tombstone m) := by
  rcases kept_cases tip received [] image member with impossible | rest
  · simp at impossible
  · exact rest

theorem viewAt_mem {s : State} {number : Nat} {m : Message}
    (member : m ∈ (viewAt s number).received) : ∃ view ∈ s.views, m ∈ view.received := by
  unfold viewAt at member
  cases found : s.views.find? (fun v => v.number == number) with
  | none => simp [found] at member
  | some view =>
    rw [found, Option.getD_some] at member
    exact ⟨view, List.mem_of_find?_eq_some found, member⟩

theorem voteOrigins_snoc {events : List Event} {event : Event}
    (all : VoteOrigins (events ++ [event])) : VoteOrigins events ∧ VoteOriginOn events event := by
  constructor
  · intro index within
    have at_ := all index (by rw [List.length_append]; omega)
    rw [List.take_append_of_le_length (Nat.le_of_lt within), List.getElem_append_left within] at at_
    exact at_
  · have at_ := all events.length (by simp)
    simpa using at_

/-- The vote origins of an audit read event by event, behind a first event that is no vote. -/
theorem voteOrigins_rebase (front : Event) (read : Event → Option Event)
    (frontFree : VoteOriginOn [] front) :
    ∀ events : List Event, VoteOrigins events →
      (∀ before event image after, events = before ++ event :: after → read event = some image →
        VoteOriginOn before event → VoteOriginOn (front :: before.filterMap read) image) →
      VoteOrigins (front :: events.filterMap read) := by
  intro events
  induction events using List.reverseRecOn with
  | nil =>
    intro _ _ index within
    have zero : index = 0 := by simpa using within
    subst zero
    simpa using frontFree
  | append_singleton rest last ih =>
    intro all each
    obtain ⟨old, fresh⟩ := voteOrigins_snoc all
    have kept := ih old (fun before event image after split =>
      each before event image (after ++ [last]) (by rw [split]; simp))
    rw [List.filterMap_append]
    cases found : read last with
    | none => simpa [List.filterMap, found] using kept
    | some image =>
      have appended := voteOrigins_append _ image kept (each rest last image [] (by simp) found fresh)
      simpa [List.filterMap, found] using appended

/-- What `rebase` did to a replica's state, by view number. `G` is the state before (its
committed tip is `tip`, committed in the floor view) and `G'` the state after. -/
structure Rebased (c : Config) (tip : Block) (G G' : State) : Prop where
  self : G'.self = G.self
  current : G'.current = G.current
  floor : G'.lastCommitted = G.lastCommitted
  evidence : G'.floorEvidence = G.floorEvidence
  delivered : G'.delivered = []
  audit : G'.audit =
    .prepare G.self G.lastCommitted [] :: G.audit.filterMap (rebaseEvent G.lastCommitted tip)
  unique : ViewsUnique G'
  named : ∀ v ∈ G'.views, v = viewAt G' v.number ∧ ∃ w ∈ G.views, w.number = v.number
  above : ∀ n, G.lastCommitted < n → rebaseView c G.self tip (viewAt G n) = some (viewAt G' n)
  floorView : (viewAt G G.lastCommitted).committed = some tip ∧
    viewAt G' G.lastCommitted = { number := G.lastCommitted, prepared := [[]], committed := some [],
                                  disabled := (viewAt G G.lastCommitted).disabled }
  below : ∀ n, n < G.lastCommitted → viewAt G' n = { number := n }

/-- **Moving the origin keeps the replica's side of the trail.** The new trail has one more
event of this member, the floor view's parent read as the committed chain, and one SEND per
tombstone, each of a faulty member. -/
theorem ghost_rebase {c : Config} {faulty : Finset Nat} {p base : Nat} {chain tip : Block}
    {trail : List Event} {G G' : State}
    (ghost : Ghost c faulty p base chain trail G) (good : Good c faulty trail)
    (honest : p ∉ faulty) (size : c.parties = 3 * c.faults + 1) (faultBound : faulty.card ≤ c.faults)
    (rebased : Rebased c tip G G') :
    ∃ extra : List Event, (∀ m, (.send m : Event) ∈ extra → m.sender ∈ faulty) ∧
      Ghost c faulty p G.lastCommitted (chain ++ tip) (trail ++ extra) G' ∧
      Good c faulty (trail ++ extra) := by
  have rules := good_faithful good size
  have roster : (Finset.range c.parties).card = 3 * c.faults + 1 := by simpa using size
  have selfG := ghost.self
  have self' : G'.self = p := rebased.self.trans selfG
  have commitEvent : (.commit p G.lastCommitted tip : Event) ∈ G.audit := by
    have recorded := ghost.output.committed G.lastCommitted tip rebased.floorView.1
    rwa [selfG] at recorded
  have commitTrail : (.commit p G.lastCommitted (chain ++ tip) : Event) ∈ trail :=
    ghost.embed _ commitEvent
  have committed' := committed_of_member (faulty := faulty) honest commitTrail
  have floorPos : 0 < G.lastCommitted := ghost.positive.2.2 _ commitEvent
  have extends_ : ∀ q v kind block, q ∉ faulty → kind ≠ .propose → G.lastCommitted < v →
      (.send ⟨q, v, kind, some (chain ++ block)⟩ : Event) ∈ trail →
      ∃ rest, strip tip block = some rest := by
    intro q v kind block hq support above member
    obtain ⟨time, output⟩ := member_trace member
    exact strip_extends (support_extends_commit rules roster faultBound committed' above hq support output)
  have ownStrips : ∀ v kind value, kind ≠ .propose → G.lastCommitted < v →
      (.send ⟨p, v, kind, value⟩ : Event) ∈ G.audit → ∃ kept, stripArgument tip value = some kept := by
    intro v kind value support above member
    cases value with
    | none => exact ⟨none, rfl⟩
    | some block =>
      obtain ⟨rest, kept⟩ := extends_ p v kind block honest support above (ghost.embed _ member)
      exact ⟨some rest, by simp [stripArgument, kept]⟩
  have inNew : ∀ event image, event ∈ G.audit →
      rebaseEvent G.lastCommitted tip event = some image → image ∈ G'.audit := by
    intro event image member read
    rw [rebased.audit]
    exact List.mem_cons_of_mem _ (List.mem_filterMap.mpr ⟨event, member, read⟩)
  have fromNew : ∀ image ∈ G'.audit, image = .prepare p G.lastCommitted [] ∨
      ∃ event ∈ G.audit, rebaseEvent G.lastCommitted tip event = some image := by
    intro image member
    rw [rebased.audit, selfG] at member
    rcases List.mem_cons.mp member with first | later
    · exact Or.inl first
    · exact Or.inr (List.mem_filterMap.mp later)
  have sendNew : ∀ m : Message, (.send m : Event) ∈ G'.audit →
      ∃ value, (.send ⟨m.sender, m.view, m.kind, value⟩ : Event) ∈ G.audit ∧
        G.lastCommitted < m.view ∧ stripArgument tip value = some m.value := by
    intro m member
    rcases fromNew _ member with impossible | ⟨event, stored, read⟩
    · cases impossible
    · obtain ⟨value, rfl, above, stripped⟩ := rebaseEvent_send read
      exact ⟨value, stored, above, stripped⟩
  have sendKept : ∀ (m : Message) (kept : Argument), (.send m : Event) ∈ G.audit →
      G.lastCommitted < m.view → stripArgument tip m.value = some kept →
      (.send ⟨m.sender, m.view, m.kind, kept⟩ : Event) ∈ G'.audit := by
    intro m kept member above stripped
    exact inNew _ _ member (by simp [rebaseEvent, above, stripped])
  have atOrBelow : ∀ n, ¬ G.lastCommitted < n →
      (viewAt G' n).voted = false ∧ (viewAt G' n).sentCandidates = [] ∧
        (viewAt G' n).sentCommit = none ∧ (viewAt G' n).received = [] := by
    intro n notAbove
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt notAbove) with below | same
    · rw [rebased.below n below]; exact ⟨rfl, rfl, rfl, rfl⟩
    · rw [same, rebased.floorView.2]; exact ⟨rfl, rfl, rfl, rfl⟩
  have voteRecorded : VoteRecorded G' := by
    intro n
    rw [self']
    by_cases above : G.lastCommitted < n
    · obtain ⟨_, voted, _⟩ := rebaseView_fields (rebased.above n above)
      rw [voted, ghost.causal.voteRecorded n, selfG]
      constructor
      · rintro ⟨block, member⟩
        obtain ⟨kept, stripped⟩ := ownStrips n .vote (some block) (by simp) above member
        cases kept with
        | none => simp [stripArgument] at stripped
        | some rest => exact ⟨rest, sendKept ⟨p, n, .vote, some block⟩ _ member above stripped⟩
      · rintro ⟨block, member⟩
        obtain ⟨value, stored, _, stripped⟩ := sendNew _ member
        cases value with
        | none => simp [stripArgument] at stripped
        | some original => exact ⟨original, stored⟩
    · rw [(atOrBelow n above).1]
      constructor
      · intro impossible; cases impossible
      · rintro ⟨block, member⟩
        obtain ⟨_, _, higher, _⟩ := sendNew _ member
        exact absurd higher above
  have voteOnce : VoteOnceAudit G' := by
    intro n first second one two
    rw [self'] at one two
    obtain ⟨a, sa, _, ka⟩ := sendNew _ one
    obtain ⟨b, sb, _, kb⟩ := sendNew _ two
    cases a with
    | none => simp [stripArgument] at ka
    | some x =>
      cases b with
      | none => simp [stripArgument] at kb
      | some y =>
        rw [← selfG] at sa sb
        have same := ghost.causal.voteOnce n x y sa sb
        subst same
        rw [ka] at kb
        simpa using kb
  have candidateRecorded : CandidateRecorded G' := by
    intro n arg
    rw [self']
    by_cases above : G.lastCommitted < n
    · obtain ⟨_, _, _, _, _, candidates, _, _⟩ := rebaseView_fields (rebased.above n above)
      constructor
      · intro member
        obtain ⟨original, stored, stripped⟩ := mapM_out _ _ _ candidates arg member
        have sent := (ghost.causal.candidateRecorded n original).mp stored
        rw [selfG] at sent
        exact sendKept ⟨p, n, .candidate, original⟩ arg sent above stripped
      · intro member
        obtain ⟨value, stored, _, stripped⟩ := sendNew _ member
        rw [← selfG] at stored
        obtain ⟨image, inside, maps⟩ := mapM_in _ _ _ candidates value
          ((ghost.causal.candidateRecorded n value).mpr stored)
        have same : image = arg := Option.some.inj (maps.symm.trans stripped)
        exact same ▸ inside
    · rw [(atOrBelow n above).2.1]
      constructor
      · intro impossible; simp at impossible
      · intro member
        obtain ⟨_, _, higher, _⟩ := sendNew _ member
        exact absurd higher above
  have commitRecorded : CommitRecorded G' := by
    intro n block
    rw [self']
    by_cases above : G.lastCommitted < n
    · obtain ⟨_, _, _, commits, _, _, _, _⟩ := rebaseView_fields (rebased.above n above)
      constructor
      · intro sent
        rw [sent] at commits
        obtain ⟨original, named, kept⟩ := stripOption_some commits
        have stored := (ghost.causal.commitRecorded n original).mp named
        rw [selfG] at stored
        exact sendKept ⟨p, n, .commit, some original⟩ (some block) stored above
          (by simp [stripArgument, kept])
      · intro member
        obtain ⟨value, stored, _, stripped⟩ := sendNew _ member
        cases value with
        | none => simp [stripArgument] at stripped
        | some original =>
          rw [← selfG] at stored
          have named := (ghost.causal.commitRecorded n original).mpr stored
          rw [named] at commits
          simp only [stripOption, stripArgument] at commits stripped
          rw [stripped] at commits
          exact (Option.some.inj commits).symm
    · rw [(atOrBelow n above).2.2.1]
      constructor
      · intro impossible; cases impossible
      · intro member
        obtain ⟨_, _, higher, _⟩ := sendNew _ member
        exact absurd higher above
  have commitLock : StateLock G' := by
    intro v member block sent arg candidate
    obtain ⟨named, _⟩ := rebased.named v member
    rw [named] at sent candidate
    by_cases above : G.lastCommitted < v.number
    · obtain ⟨_, _, _, commits, _, candidates, _, _⟩ := rebaseView_fields (rebased.above v.number above)
      rw [sent] at commits
      obtain ⟨original, sentOld, kept⟩ := stripOption_some commits
      obtain ⟨originalArg, stored, stripped⟩ := mapM_out _ _ _ candidates arg candidate
      have locked := viewAt_locked G v.number ghost.causal.commitLock original sentOld originalArg stored
      subst locked
      simp only [stripArgument, kept, Option.map_some, Option.some.injEq] at stripped
      exact stripped.symm
    · rw [(atOrBelow v.number above).2.2.1] at sent
      cases sent
  have preparedRecorded : PreparedRecorded G' := by
    intro n block member
    rw [self']
    by_cases above : G.lastCommitted < n
    · obtain ⟨_, _, _, _, _, _, prepared, _⟩ := rebaseView_fields (rebased.above n above)
      obtain ⟨original, stored, kept⟩ := mapM_out _ _ _ prepared block member
      have old := ghost.history.prepared n original stored
      rw [selfG] at old
      exact inNew _ _ old (by simp [rebaseEvent, above, kept])
    · rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt above) with below | same
      · rw [rebased.below n below] at member; simp at member
      · rw [same, rebased.floorView.2] at member
        have empty : block = [] := by simpa using member
        rw [empty, same, rebased.audit, selfG]
        exact List.mem_cons_self
  have disabledRecorded : DisabledRecorded G' := by
    intro n disabled
    rw [self']
    have live : G.lastCommitted ≤ n := by
      by_contra dead
      rw [rebased.below n (by omega)] at disabled
      simp at disabled
    have old : (viewAt G n).disabled = true := by
      rcases Nat.lt_or_eq_of_le live with above | same
      · obtain ⟨_, _, kept, _⟩ := rebaseView_fields (rebased.above n above)
        rwa [kept] at disabled
      · rw [← same, rebased.floorView.2] at disabled
        rw [← same]; exact disabled
    have stored := ghost.history.disabled n old
    rw [selfG] at stored
    exact inNew _ _ stored (by simp [rebaseEvent, live])
  have committedRecorded : CommittedRecorded G' := by
    intro n block committed
    rw [self']
    by_cases above : G.lastCommitted < n
    · obtain ⟨_, _, _, _, commits, _, _, _⟩ := rebaseView_fields (rebased.above n above)
      rw [committed] at commits
      obtain ⟨original, named, kept⟩ := stripOption_some commits
      have old := ghost.output.committed n original named
      rw [selfG] at old
      exact inNew _ _ old (by simp [rebaseEvent, above, kept])
    · rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt above) with below | same
      · rw [rebased.below n below] at committed; simp at committed
      · rw [same, rebased.floorView.2] at committed
        have empty : block = [] := by simpa using committed.symm
        rw [empty, same]
        exact inNew _ _ commitEvent (by simp [rebaseEvent])
  have origins : VoteOrigins G'.audit := by
    rw [rebased.audit]
    apply voteOrigins_rebase (.prepare G.self G.lastCommitted []) (rebaseEvent G.lastCommitted tip)
      True.intro G.audit ghost.origins
    intro before event image after split read origin
    have inBefore : ∀ e ∈ before, e ∈ G.audit := fun e inside => by rw [split]; simp [inside]
    have keptBefore : ∀ e img, e ∈ before → rebaseEvent G.lastCommitted tip e = some img →
        img ∈ (.prepare G.self G.lastCommitted [] : Event) ::
          before.filterMap (rebaseEvent G.lastCommitted tip) :=
      fun e img inside kept => List.mem_cons_of_mem _ (List.mem_filterMap.mpr ⟨e, inside, kept⟩)
    cases image with
    | send message =>
      obtain ⟨sender, n, kind, value⟩ := message
      obtain ⟨original, named, above, stripped⟩ := rebaseEvent_send read
      subst named
      cases kind <;> cases value <;> try exact True.intro
      rename_i rest
      cases original with
      | none => simp [stripArgument] at stripped
      | some block =>
        simp only [stripArgument, Option.map_eq_some_iff, Option.some.injEq] at stripped
        obtain ⟨found, kept, same⟩ := stripped
        subst same
        obtain ⟨whole, nonemptyRest⟩ := strip_eq kept
        have owner : sender = p := by
          have stored : (.send ⟨sender, n, .vote, some block⟩ : Event) ∈ G.audit := by rw [split]; simp
          have owned := ghost.owned _ stored
          simpa [eventOwner, selfG] using owned
        subst owner
        have last : block.dropLast = tip ++ found.dropLast := by
          rw [whole]; exact List.dropLast_append_of_ne_nil nonemptyRest
        simp only [VoteOriginOn] at origin ⊢
        rcases origin with safe | prepared
        · left
          obtain ⟨_, previous, older, parent, skipped⟩ := (safeAt_iff _ _ _ _).mp safe
          rcases Nat.lt_trichotomy previous G.lastCommitted with below | same | higher
          · exfalso
            have disabled := ghost.embed _ (inBefore _ (skipped G.lastCommitted below above))
            obtain ⟨time, output⟩ := member_trace disabled
            exact committed_not_disabled rules roster faultBound committed' honest output
          · have stored : (.prepare sender previous block.dropLast : Event) ∈ before :=
              parent.resolve_left (fun genesis => by have := genesis.1; omega)
            have inTrail := ghost.embed _ (inBefore _ stored)
            rw [same] at inTrail
            obtain ⟨t1, prep⟩ := member_trace inTrail
            obtain ⟨t2, comm⟩ := member_trace commitTrail
            have equal := committed_excludes_other_prepare rules roster faultBound honest honest comm prep
            have emptyParent : found.dropLast = [] := by
              rw [last] at equal
              have cancelled := List.append_cancel_left equal
              simpa using cancelled
            refine (safeAt_iff _ _ _ _).mpr ⟨nonemptyRest, G.lastCommitted, above, Or.inr ?_, ?_⟩
            · rw [emptyParent, selfG]; exact List.mem_cons_self
            · intro view low high
              exact keptBefore _ _ (skipped view (by omega) high)
                (by have live : G.lastCommitted ≤ view := by omega
                    simp [rebaseEvent, live])
          · have stored : (.prepare sender previous block.dropLast : Event) ∈ before :=
              parent.resolve_left (fun genesis => by have := genesis.1; omega)
            have inTrail := ghost.embed _ (inBefore _ stored)
            obtain ⟨t1, prep⟩ := member_trace inTrail
            obtain ⟨q, hq, earlier, _, vote⟩ := prepared_has_honest_vote rules faultBound honest prep
            obtain ⟨parentRest, keptParent⟩ :=
              strip_extends (vote_extends_commit rules roster faultBound committed' higher hq vote)
            have sameParent : parentRest = found.dropLast := by
              obtain ⟨parentWhole, _⟩ := strip_eq keptParent
              rw [last] at parentWhole
              exact (List.append_cancel_left parentWhole).symm
            subst sameParent
            refine (safeAt_iff _ _ _ _).mpr ⟨nonemptyRest, previous, older, Or.inr ?_, ?_⟩
            · exact keptBefore _ _ stored (by simp [rebaseEvent, higher, keptParent])
            · intro view low high
              exact keptBefore _ _ (skipped view low high)
                (by have live : G.lastCommitted ≤ view := by omega
                    simp [rebaseEvent, live])
        · exact Or.inr (keptBefore _ _ prepared (by simp [rebaseEvent, above, kept]))
    | _ => exact True.intro
  have positive : Positive G' := by
    refine ⟨by rw [rebased.current]; exact ghost.positive.1, ?_, ?_⟩
    · intro v member
      obtain ⟨_, w, inside, same⟩ := rebased.named v member
      rw [← same]; exact ghost.positive.2.1 w inside
    · intro event member
      rcases fromNew event member with first | ⟨original, stored, read⟩
      · rw [first]; exact floorPos
      · exact rebaseEvent_positive read (ghost.positive.2.2 _ stored)
  have receivedCases : ∀ v ∈ G'.views, ∀ m ∈ v.received, G.lastCommitted < v.number ∧
      ((∃ original ∈ (viewAt G v.number).received, stripArgument tip original.value = some m.value ∧
          m = ⟨original.sender, original.view, original.kind, m.value⟩) ∨
        (∃ original ∈ (viewAt G v.number).received, stripArgument tip original.value = none ∧
          original.kind = .vote ∧ m = tombstone original)) := by
    intro v member m received
    obtain ⟨named, _⟩ := rebased.named v member
    rw [named] at received
    by_cases above : G.lastCommitted < v.number
    · obtain ⟨_, _, _, _, _, _, _, kept⟩ := rebaseView_fields (rebased.above v.number above)
      rw [kept] at received
      exact ⟨above, keptReceived_cases received⟩
    · rw [(atOrBelow v.number above).2.2.2] at received
      simp at received
  have scope : Scoped c G' := by
    refine ⟨by rw [rebased.self]; exact ghost.scope.1, ?_⟩
    intro v member m received
    obtain ⟨_, cases_⟩ := receivedCases v member m received
    rcases cases_ with ⟨original, stored, _, named⟩ | ⟨original, stored, _, _, named⟩
    · have old := viewAt_scoped ghost.scope v.number original stored
      rw [named]; exact old
    · have old := viewAt_scoped ghost.scope v.number original stored
      rw [named]; exact old
  have owned : OwnedAudit G' := by
    intro event member
    rw [self']
    rcases fromNew event member with first | ⟨original, stored, read⟩
    · rw [first]; rfl
    · rw [rebaseEvent_owner read, ghost.owned _ stored, selfG]
  refine ⟨(.prepare p G.lastCommitted (chain ++ tip) : Event) :: G'.views.flatMap (fun v =>
    (v.received.filter fun m => m.kind == .vote && m.value == some []).map
      fun m => (.send (liftMessage (chain ++ tip) m) : Event)), ?_⟩
  have tombFaulty : ∀ m, (.send m : Event) ∈ (.prepare p G.lastCommitted (chain ++ tip) : Event) ::
      G'.views.flatMap (fun v => (v.received.filter fun m => m.kind == .vote && m.value == some []).map
        fun m => (.send (liftMessage (chain ++ tip) m) : Event)) → m.sender ∈ faulty := by
    intro m member
    rcases List.mem_cons.mp member with impossible | later
    · cases impossible
    · obtain ⟨v, stored, inner⟩ := List.mem_flatMap.mp later
      obtain ⟨tomb, filtered, lifted⟩ := List.mem_map.mp inner
      obtain ⟨received, marked⟩ := List.mem_filter.mp filtered
      simp only [AuditEvent.send.injEq] at lifted
      subst lifted
      rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at marked
      obtain ⟨above, cases_⟩ := receivedCases v stored tomb received
      rcases cases_ with ⟨original, _, stripped, _⟩ | ⟨original, inside, dropped, vote, named⟩
      · exfalso
        rw [marked.2] at stripped
        cases value : original.value with
        | none => rw [value] at stripped; simp [stripArgument] at stripped
        | some block =>
          rw [value] at stripped
          simp only [stripArgument, Option.map_eq_some_iff, Option.some.injEq] at stripped
          obtain ⟨rest, kept, empty⟩ := stripped
          exact (strip_eq kept).2 empty
      · by_contra correct
        have senderSame : (liftMessage (chain ++ tip) tomb).sender = original.sender := by rw [named]; rfl
        rw [senderSame] at correct
        obtain ⟨view, viewStored, viewReceived⟩ := viewAt_mem inside
        have inTrail := ghost.received view viewStored original viewReceived
        have inView := viewAt_scoped ghost.scope v.number original inside
        obtain ⟨sender, number, kind, value⟩ := original
        simp only at vote inView dropped correct
        subst vote
        cases value with
        | none => simp [stripArgument] at dropped
        | some block =>
          obtain ⟨rest, kept⟩ := extends_ sender number .vote block correct (by simp)
            (by rw [inView.2]; exact above) inTrail
          simp [stripArgument, kept] at dropped
  refine ⟨tombFaulty, ?_, ?_⟩
  · exact
      { self := self'
        causal := ⟨rebased.unique, voteRecorded, voteOnce, candidateRecorded, commitRecorded, commitLock⟩
        history := ⟨preparedRecorded, disabledRecorded⟩
        origins := origins
        positive := positive
        scope := scope
        output := ⟨committedRecorded, fun block member => by rw [rebased.delivered] at member; simp at member⟩
        owned := owned
        live := by rw [rebased.floor, rebased.current]; exact ghost.live
        baseLe := by rw [rebased.floor]
        committed := committed_extend committed'
        embed := fun event member => by
          rcases fromNew event member with first | ⟨original, stored, read⟩
          · rw [first]
            exact List.mem_append.mpr (Or.inr (by simp [liftEvent]))
          · rw [rebaseEvent_lift read]
            exact List.mem_append.mpr (Or.inl (ghost.embed _ stored))
        received := fun v member m received => by
          obtain ⟨above, cases_⟩ := receivedCases v member m received
          rcases cases_ with ⟨original, inside, stripped, named⟩ | ⟨original, _, _, vote, named⟩
          · obtain ⟨view, viewStored, viewReceived⟩ := viewAt_mem inside
            have inTrail := ghost.received view viewStored original viewReceived
            have same : liftMessage (chain ++ tip) m = liftMessage chain original := by
              rw [named]
              simp only [liftMessage, stripArgument_lift stripped]
            rw [same]
            exact List.mem_append.mpr (Or.inl inTrail)
          · refine List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ (List.mem_flatMap.mpr
              ⟨v, member, List.mem_map.mpr ⟨m, List.mem_filter.mpr ⟨received, ?_⟩, rfl⟩⟩)))
            rw [named]
            simp [tombstone, vote]
        complete := fun v kind value kindOK above member => by
          rw [rebased.floor] at above
          rcases List.mem_append.mp member with inside | added
          · obtain ⟨relative, stored, same⟩ := ghost.complete v kind value kindOK above inside
            have support : kind ≠ .propose := by rcases kindOK with rfl | rfl | rfl <;> simp
            obtain ⟨kept, stripped⟩ := ownStrips v kind relative support above stored
            exact ⟨kept, sendKept ⟨p, v, kind, relative⟩ kept stored above stripped,
              (stripArgument_lift stripped).trans same⟩
          · exact absurd (tombFaulty _ added) honest
        evidenceViews := by rw [rebased.evidence, rebased.floor]; exact ghost.evidenceViews }
  · have prepared : Good c faulty (trail ++ [(.prepare p G.lastCommitted (chain ++ tip) : Event)]) := by
      have old : ∀ {q v kind value}, (.send ⟨q, v, kind, value⟩ : Event) ∈
          trail ++ [(.prepare p G.lastCommitted (chain ++ tip) : Event)] →
          (.send ⟨q, v, kind, value⟩ : Event) ∈ trail := by
        intro q v kind value member
        rcases List.mem_append.mp member with inside | added
        · exact inside
        · simp at added
      apply good_append good
      · intro index within owner _ _
        have zero : index = 0 := by simpa using within
        subst zero
        obtain ⟨t, tw, same⟩ := List.mem_iff_getElem.mp commitTrail
        have cause := (good.events t tw p (by rw [same]; rfl) honest).1
        rw [same] at cause
        refine ⟨?_, True.intro, floorPos⟩
        simp only [EventSupported, List.take_zero, List.append_nil, List.getElem_cons_zero] at cause ⊢
        exact Or.inr (Or.inr (evidence_prefix cause (List.take_prefix _ _)))
      · intro q v x y honestOwner first second
        exact good.voteOnce q v x y honestOwner (old first) (old second)
      · intro q v x a honestOwner first second
        exact good.lock q v x a honestOwner (old first) (old second)
    have all := good_append_free prepared (extra := G'.views.flatMap (fun v =>
      (v.received.filter fun m => m.kind == .vote && m.value == some []).map
        fun m => (.send (liftMessage (chain ++ tip) m) : Event))) (by
      intro event member owner owned_
      obtain ⟨v, _, inner⟩ := List.mem_flatMap.mp member
      obtain ⟨tomb, _, lifted⟩ := List.mem_map.mp inner
      subst lifted
      simp only [eventOwner, Option.some.injEq] at owned_
      rw [← owned_]
      exact tombFaulty _ (List.mem_cons_of_mem _ member))
    simpa [List.append_assoc] using all

#assert_axioms ghost_rebase

end Minidregg.Kernel.GenericSimplexRebaseGhost
