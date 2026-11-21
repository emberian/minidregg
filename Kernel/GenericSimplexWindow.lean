/- The view window of the agreement engine. A replica keeps a view record only for views up
to `horizon` (`Config.window` above its current view). Kernel-only. Stated and proved here:

* `ingest_beyond`: a member's message for a view above the horizon, other than a COMMIT,
  changes nothing but the `ahead` note (`noteAhead_frame`): no view record, no send, no relay;
* `noteAhead_unique`, `noteAhead_members`: `ahead` holds one entry per member, so at most
  `parties` entries whatever a Byzantine member names;
* `ingest_within`: a message for a view above the floor and within the horizon that this
  replica has not received is registered exactly as it was before the window existed
  (`ingest_within_propose` for the leader's proposal). The window refuses nothing a
  replica within `window` views of the sender needs;
* `ingest_over_cap`: a member that has `Config.cap` messages of one kind in a view record
  adds no more.

What the window drops is recovered by `serveViews`; that it suffices is executed in
`Verify/GenericSimplexWindow.lean` and is part of the liveness argument, not proved. -/
import Kernel.GenericSimplex

namespace Minidregg.Kernel.GenericSimplexWindow
open Minidregg.Kernel.GenericSimplex
set_option autoImplicit false

theorem floor_le_horizon (c : Config) (s : State) : s.lastCommitted ≤ horizon c s := by
  unfold horizon; omega

theorem current_le_horizon (c : Config) (s : State) : s.current ≤ horizon c s := by
  unfold horizon; omega

/-- **Above the horizon nothing is kept** but a COMMIT. -/
theorem ingest_beyond (c : Config) (s : State) (m : Message)
    (member : m.sender < c.parties) (far : horizon c s < m.view) (other : m.kind ≠ .commit) :
    ingest c s m = noteAhead s m.sender m.view := by
  have kind : (m.kind != .commit) = true := by
    cases named : m.kind <;> first | exact absurd named other | rfl
  have floor := floor_le_horizon c s
  have guard : (decide (m.sender ≥ c.parties) || m.view == 0) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
    omega
  unfold ingest
  rw [if_neg (by rw [guard]; exact Bool.false_ne_true), if_neg (by omega),
    if_pos (by rw [kind, Bool.and_true]; exact decide_eq_true far)]

theorem noteAhead_frame (s : State) (sender view : Nat) :
    (noteAhead s sender view).views = s.views ∧ (noteAhead s sender view).outbox = s.outbox ∧
    (noteAhead s sender view).relay = s.relay ∧ (noteAhead s sender view).current = s.current ∧
    (noteAhead s sender view).lastCommitted = s.lastCommitted ∧
    (noteAhead s sender view).checked = s.checked ∧ (noteAhead s sender view).offers = s.offers := by
  unfold noteAhead
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- One `ahead` entry per member. -/
def AheadUnique (s : State) : Prop := (s.ahead.map (·.1)).Nodup

theorem noteAhead_unique (s : State) (sender view : Nat) (old : AheadUnique s) :
    AheadUnique (noteAhead s sender view) := by
  unfold noteAhead
  split
  · exact old
  · unfold AheadUnique
    dsimp only
    rw [List.map_append, List.nodup_append]
    refine ⟨(old.sublist (List.Sublist.map _ List.filter_sublist)), List.pairwise_singleton _ _, ?_⟩
    intro who inside other last
    rw [List.map_singleton, List.mem_singleton] at last
    obtain ⟨entry, member, same⟩ := List.mem_map.mp inside
    have differs := (List.mem_filter.mp member).2
    rw [last, ← same]
    simpa using differs

theorem noteAhead_members (s : State) (sender view parties : Nat) (enrolled : sender < parties)
    (old : ∀ entry ∈ s.ahead, entry.1 < parties) :
    ∀ entry ∈ (noteAhead s sender view).ahead, entry.1 < parties := by
  unfold noteAhead
  split
  · exact old
  · intro entry inside
    rcases List.mem_append.mp inside with kept | new
    · exact old entry (List.mem_filter.mp kept).1
    · rw [List.mem_singleton.mp new]; exact enrolled

/-- **Within the horizon the window refuses nothing.** A message this replica has not
received, for a view above its floor and at most `window` above its current view, is
registered. -/
theorem ingest_within (c : Config) (s : State) (m : Message)
    (member : m.sender < c.parties) (above : s.lastCommitted < m.view)
    (near : m.view ≤ horizon c s) (other : m.kind ≠ .propose)
    (valued : m.kind = .vote ∨ m.kind = .commit → m.value.isSome = true)
    (fresh : (viewAt s m.view).received.contains m = false)
    (room : overCap c s m = false) :
    ingest c s m = register s m := by
  have guard : (decide (m.sender ≥ c.parties) || m.view == 0) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
    omega
  have unvalued : ((m.kind == .propose || m.kind == .vote || m.kind == .commit) && m.value.isNone) = false := by
    cases kind : m.kind with
    | propose => exact absurd kind other
    | vote =>
      obtain ⟨block, same⟩ := Option.isSome_iff_exists.mp (valued (Or.inl kind))
      rw [same]; rfl
    | commit =>
      obtain ⟨block, same⟩ := Option.isSome_iff_exists.mp (valued (Or.inr kind))
      rw [same]; rfl
    | candidate => rfl
    | ready => rfl
  have notPropose : (m.kind == .propose) = false := by
    cases kind : m.kind <;> first | exact absurd kind other | rfl
  have notRepeat : (m.kind == .candidate && m.value.isNone && decide (m.view < s.current) &&
      (viewAt s m.view).received.contains m) = false := by
    rw [fresh, Bool.and_false]
  unfold ingest
  rw [if_neg (by rw [guard]; exact Bool.false_ne_true), if_neg (by omega),
    if_neg (by rw [Bool.and_eq_true, decide_eq_true_eq]; omega),
    if_neg (by rw [unvalued]; exact Bool.false_ne_true),
    if_neg (by rw [notPropose]; exact Bool.false_ne_true),
    if_neg (by rw [notRepeat]; exact Bool.false_ne_true),
    if_neg (by rw [room]; exact Bool.false_ne_true)]

/-- **A member's share of a view record is bounded.** Once a member has `Config.cap`
messages of one kind in a view record, a further one of that kind changes nothing: no
record, no send, no relay. (The leader's PROPOSE is not a received message; a view keeps
one.) -/
theorem ingest_over_cap (c : Config) (s : State) (m : Message)
    (member : m.sender < c.parties) (above : s.lastCommitted < m.view)
    (near : m.view ≤ horizon c s) (other : m.kind ≠ .propose)
    (fresh : (viewAt s m.view).received.contains m = false)
    (full : overCap c s m = true) :
    ingest c s m = s := by
  have guard : (decide (m.sender ≥ c.parties) || m.view == 0) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
    omega
  have notPropose : (m.kind == .propose) = false := by
    cases kind : m.kind <;> first | exact absurd kind other | rfl
  have notRepeat : (m.kind == .candidate && m.value.isNone && decide (m.view < s.current) &&
      (viewAt s m.view).received.contains m) = false := by
    rw [fresh, Bool.and_false]
  unfold ingest
  rw [if_neg (by rw [guard]; exact Bool.false_ne_true), if_neg (by omega),
    if_neg (by rw [Bool.and_eq_true, decide_eq_true_eq]; omega)]
  split
  · rfl
  · rw [if_neg (by rw [notPropose]; exact Bool.false_ne_true),
      if_neg (by rw [notRepeat]; exact Bool.false_ne_true)]

/-- The leader's first proposal for a view within the horizon is recorded. -/
theorem ingest_within_propose (c : Config) (s : State) (m : Message)
    (member : m.sender < c.parties) (above : s.lastCommitted < m.view)
    (near : m.view ≤ horizon c s) (propose : m.kind = .propose)
    (valued : m.value.isSome = true) (leader : m.sender = c.leader m.view)
    (first : (viewAt s m.view).proposal = none) :
    ingest c s m = putView s { viewAt s m.view with proposal := m.value } := by
  have guard : (decide (m.sender ≥ c.parties) || m.view == 0) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
    omega
  have unvalued : ((m.kind == .propose || m.kind == .vote || m.kind == .commit) && m.value.isNone) = false := by
    obtain ⟨block, same⟩ := Option.isSome_iff_exists.mp valued
    rw [same]; exact Bool.and_false _
  have proposes : (m.kind == .propose) = true := by rw [propose]; rfl
  have leads : (m.sender != c.leader m.view) = false := by rw [← leader]; exact bne_self_eq_false _
  unfold ingest
  rw [if_neg (by rw [guard]; exact Bool.false_ne_true), if_neg (by omega),
    if_neg (by rw [Bool.and_eq_true, decide_eq_true_eq]; omega),
    if_neg (by rw [unvalued]; exact Bool.false_ne_true), if_pos proposes,
    if_neg (by rw [leads]; exact Bool.false_ne_true)]
  dsimp only
  rw [first]
  rfl

/-- A tick, up to the timer's decision: local actions drained, the clock advanced. -/
def ticked (c : Config) (s : State) (now : Nat) : State :=
  { pump c c.pumpBudget s with now := max (pump c c.pumpBudget s).now now }

/-- **An idle view's timer does nothing but move its deadline.** When the replica has no
reason to leave its view (`wantsOut`), a tick is the drain of local actions before and
after, with the deadline set one whole timeout ahead: the timer asks for no disable and
repeats no CANDIDATE(⊥). (That the two drains send nothing in a quiescent state is not
proved here; executed: `Verify.GenericSimplexWindow`, `idle.sent == oneOp.sent`.) -/
theorem tick_idle (c : Config) (s : State) (now : Nat)
    (running : (!c.wellFormed || decide (s.self ≥ c.parties) || s.failed) = false)
    (idle : wantsOut c (ticked c s now) = false) :
    step c s (.tick now) = pump c c.pumpBudget
      { ticked c s now with
        deadline := (ticked c s now).now + viewTimeout c (ticked c s now) (ticked c s now).current } := by
  unfold step
  rw [if_neg (by rw [running]; exact Bool.false_ne_true)]
  show pump c c.pumpBudget (if (!wantsOut c (ticked c s now)) = true then _ else _) = _
  rw [if_pos (by rw [idle]; rfl)]
  rfl

end Minidregg.Kernel.GenericSimplexWindow
