import Kernel.GenericSimplex

/-! # Erasure: a running replica forgets everything at or below its floor

`step` is the specification transition: its states keep every view ever touched and the
whole audit, and every safety theorem is about them. `liveStep` is `step` followed by
`forget` (drop the views at or below the floor, drop the audit). This file proves that no
rule reads what `forget` drops: `forget (step c s i) = forget (step c (forget s) i)`
(`step_erase`). So the states of a replica running `liveStep` are exactly the `forget`
images of the states of the same replica running `step` on the same inputs
(`liveStep_run`): same sends, same commits, same floor, same live views. -/

namespace Minidregg.Kernel.GenericSimplexErasure
open Minidregg.Kernel.GenericSimplex
set_option autoImplicit false

/-! ## Lists of views -/

def putList (views : List View) (v : View) : List View :=
  if views.any (fun old => old.number == v.number) then
    views.map (fun old => if old.number == v.number then v else old)
  else views ++ [v]

theorem putView_views (s : State) (v : View) : (putView s v).views = putList s.views v := rfl

theorem find_live (floor number : Nat) (views : List View) (live : floor ≤ number) :
    (views.filter (fun v => floor ≤ v.number)).find? (fun v => v.number == number) =
      views.find? (fun v => v.number == number) := by
  induction views with
  | nil => rfl
  | cons head rest ih =>
    by_cases keep : floor ≤ head.number
    · simp [List.find?_cons, keep, ih]
    · have other : (head.number == number) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; omega
      simp [keep, other, ih]

theorem any_live (floor number : Nat) (views : List View) (live : floor ≤ number) :
    (views.filter (fun v => floor ≤ v.number)).any (fun v => v.number == number) =
      views.any (fun v => v.number == number) := by
  induction views with
  | nil => rfl
  | cons head rest ih =>
    by_cases keep : floor ≤ head.number
    · simp [List.any_cons, keep, ih]
    · have other : (head.number == number) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; omega
      simp [keep, other, ih]

theorem filter_replace (floor : Nat) (views : List View) (v : View) (live : floor ≤ v.number) :
    (views.map (fun old => if old.number == v.number then v else old)).filter
        (fun w => floor ≤ w.number) =
      (views.filter (fun w => floor ≤ w.number)).map
        (fun old => if old.number == v.number then v else old) := by
  induction views with
  | nil => rfl
  | cons head rest ih =>
    simp only [beq_iff_eq] at ih
    by_cases same : head.number = v.number
    · have keep : floor ≤ head.number := by omega
      simp [same, live, ih]
    · by_cases keep : floor ≤ head.number <;> simp [same, keep, ih]

theorem filter_putList (floor : Nat) (views : List View) (v : View) (live : floor ≤ v.number) :
    (putList views v).filter (fun w => floor ≤ w.number) =
      putList (views.filter (fun w => floor ≤ w.number)) v := by
  unfold putList
  rw [any_live floor v.number views live]
  split
  · exact filter_replace floor views v live
  · simp [List.filter_append, live]

/-! ## `forget` and the reads it does not disturb -/

theorem forget_forget (s : State) : forget (forget s) = forget s := by
  have idem : ∀ views : List View,
      (views.filter (fun v => s.lastCommitted ≤ v.number)).filter
        (fun v => s.lastCommitted ≤ v.number) =
      views.filter (fun v => s.lastCommitted ≤ v.number) := by
    intro views
    induction views with
    | nil => rfl
    | cons head rest ih => by_cases keep : s.lastCommitted ≤ head.number <;> simp [keep, ih]
  unfold forget
  dsimp only
  rw [idem]

theorem viewAt_forget (s : State) (number : Nat) (live : s.lastCommitted ≤ number) :
    viewAt (forget s) number = viewAt s number := by
  unfold viewAt forget
  exact congrArg (fun found => found.getD { number := number })
    (find_live s.lastCommitted number s.views live)

theorem viewAt_number (s : State) (number : Nat) : (viewAt s number).number = number := by
  unfold viewAt
  cases found : s.views.find? (fun v => v.number == number) with
  | none => rfl
  | some v =>
    have matched := List.find?_some found
    simpa using matched

theorem forget_putView (s : State) (v : View) (live : s.lastCommitted ≤ v.number) :
    forget (putView s v) = putView (forget s) v := by
  have views := filter_putList s.lastCommitted s.views v live
  unfold forget putView
  simp only [putList] at views
  simp only [views]

/-- Two states a running replica cannot tell apart. -/
abbrev Same (s t : State) : Prop := forget s = forget t

theorem same_forget (s : State) : Same s (forget s) := (forget_forget s).symm

theorem same_self {s t : State} (same : Same s t) : s.self = t.self := by
  have fields : (forget s).self = (forget t).self := congrArg State.self same
  exact fields
theorem same_current {s t : State} (same : Same s t) : s.current = t.current := by
  have fields : (forget s).current = (forget t).current := congrArg State.current same
  exact fields
theorem same_deadline {s t : State} (same : Same s t) : s.deadline = t.deadline := by
  have fields : (forget s).deadline = (forget t).deadline := congrArg State.deadline same
  exact fields
theorem same_now {s t : State} (same : Same s t) : s.now = t.now := by
  have fields : (forget s).now = (forget t).now := congrArg State.now same
  exact fields
theorem same_checked {s t : State} (same : Same s t) : s.checked = t.checked := by
  have fields : (forget s).checked = (forget t).checked := congrArg State.checked same
  exact fields
theorem same_offers {s t : State} (same : Same s t) : s.offers = t.offers := by
  have fields : (forget s).offers = (forget t).offers := congrArg State.offers same
  exact fields
theorem same_outbox {s t : State} (same : Same s t) : s.outbox = t.outbox := by
  have fields : (forget s).outbox = (forget t).outbox := congrArg State.outbox same
  exact fields
theorem same_delivered {s t : State} (same : Same s t) : s.delivered = t.delivered := by
  have fields : (forget s).delivered = (forget t).delivered := congrArg State.delivered same
  exact fields
theorem same_committedTip {s t : State} (same : Same s t) : s.committedTip = t.committedTip := by
  have fields : (forget s).committedTip = (forget t).committedTip := congrArg State.committedTip same
  exact fields
theorem same_needsPoll {s t : State} (same : Same s t) : s.needsPoll = t.needsPoll := by
  have fields : (forget s).needsPoll = (forget t).needsPoll := congrArg State.needsPoll same
  exact fields
theorem same_failed {s t : State} (same : Same s t) : s.failed = t.failed := by
  have fields : (forget s).failed = (forget t).failed := congrArg State.failed same
  exact fields
theorem same_lastCommitted {s t : State} (same : Same s t) : s.lastCommitted = t.lastCommitted := by
  have fields : (forget s).lastCommitted = (forget t).lastCommitted := congrArg State.lastCommitted same
  exact fields
theorem same_floorEvidence {s t : State} (same : Same s t) : s.floorEvidence = t.floorEvidence := by
  have fields : (forget s).floorEvidence = (forget t).floorEvidence := congrArg State.floorEvidence same
  exact fields
theorem same_served {s t : State} (same : Same s t) : s.served = t.served := by
  have fields : (forget s).served = (forget t).served := congrArg State.served same
  exact fields
theorem same_relay {s t : State} (same : Same s t) : s.relay = t.relay := by
  have fields : (forget s).relay = (forget t).relay := congrArg State.relay same
  exact fields
theorem same_ahead {s t : State} (same : Same s t) : s.ahead = t.ahead := by
  have fields : (forget s).ahead = (forget t).ahead := congrArg State.ahead same
  exact fields

theorem same_viewAt_floor {s t : State} (same : Same s t) (number : Nat)
    (live : s.lastCommitted ≤ number) : viewAt s number = viewAt t number := by
  rw [← viewAt_forget s number live, same, viewAt_forget t number (same_lastCommitted same ▸ live)]

theorem same_viewAt {s t : State} (same : Same s t) (number : Nat)
    (live : s.lastCommitted < number) : viewAt s number = viewAt t number :=
  same_viewAt_floor same number (Nat.le_of_lt live)

theorem same_putView {s t : State} (same : Same s t) (v : View)
    (live : s.lastCommitted < v.number) : Same (putView s v) (putView t v) := by
  unfold Same
  rw [forget_putView s v (Nat.le_of_lt live),
    forget_putView t v (Nat.le_of_lt (same_lastCommitted same ▸ live)), same]

theorem same_validBlock {s t : State} (same : Same s t) (block : Block) :
    validBlock s block = validBlock t block := by
  unfold validBlock
  rw [same_checked same]

theorem filter_above (floor number : Nat) (above : floor ≤ number) (views : List View) :
    views.filter (fun v => number ≤ v.number) =
      (views.filter (fun v => floor ≤ v.number)).filter (fun v => number ≤ v.number) := by
  induction views with
  | nil => rfl
  | cons head rest ih =>
    by_cases high : number ≤ head.number
    · have keep : floor ≤ head.number := by omega
      simp [high, keep, ih]
    · by_cases keep : floor ≤ head.number <;> simp [high, keep, ih]

theorem same_views {s t : State} (same : Same s t) :
    s.views.filter (fun v => s.lastCommitted ≤ v.number) =
      t.views.filter (fun v => s.lastCommitted ≤ v.number) := by
  have fields : s.views.filter (fun v => s.lastCommitted ≤ v.number) =
      t.views.filter (fun v => t.lastCommitted ≤ v.number) := congrArg State.views same
  rw [← same_lastCommitted same] at fields
  exact fields

/-- Raising the floor of both keeps them indistinguishable. -/
theorem same_raise {s t : State} (same : Same s t) (number : Nat) (above : s.lastCommitted ≤ number)
    (evidence : List Message) :
    Same { s with lastCommitted := number, served := [], floorEvidence := evidence }
      { t with lastCommitted := number, served := [], floorEvidence := evidence } := by
  have high : s.views.filter (fun v => number ≤ v.number) = t.views.filter (fun v => number ≤ v.number) := by
    rw [filter_above s.lastCommitted number above s.views, filter_above s.lastCommitted number above t.views,
      same_views same]
  unfold Same forget
  dsimp only
  rw [high, same_self same, same_current same, same_deadline same, same_now same, same_checked same,
    same_offers same, same_outbox same, same_delivered same, same_committedTip same,
    same_needsPoll same, same_failed same, same_relay same, same_ahead same]

/-! ## Floor and current are untouched by the rules that do not commit -/

theorem register_floor (s : State) (m : Message) : (register s m).lastCommitted = s.lastCommitted := rfl
theorem broadcast_floor (s : State) (number : Nat) (kind : Kind) (value : Argument) :
    (broadcast s number kind value).lastCommitted = s.lastCommitted := rfl
theorem broadcast_current (s : State) (number : Nat) (kind : Kind) (value : Argument) :
    (broadcast s number kind value).current = s.current := rfl
theorem clear_floor (s : State) (number : Nat) (value : Argument) :
    (clear s number value).lastCommitted = s.lastCommitted := by
  unfold clear
  cases value <;> dsimp only <;> split <;> rfl
theorem doCommit_floor (s : State) (number : Nat) (block : Block) :
    (doCommit s number block).lastCommitted = s.lastCommitted := by
  unfold doCommit
  dsimp only
  repeat' split
  all_goals first | rfl | exact clear_floor s number (some block)
theorem sendCandidate_floor (s : State) (number : Nat) (arg : Argument) :
    (sendCandidate s number arg).lastCommitted = s.lastCommitted := by
  unfold sendCandidate
  dsimp only
  split <;> rfl
theorem castVote_floor (s : State) (number : Nat) (block : Block) :
    (castVote s number block).lastCommitted = s.lastCommitted := by
  unfold castVote
  dsimp only
  split <;> rfl
theorem castVote_current (s : State) (number : Nat) (block : Block) :
    (castVote s number block).current = s.current := by
  unfold castVote
  dsimp only
  split <;> rfl

/-! ## Every rule acts the same on indistinguishable states -/

theorem register_same {s t : State} (same : Same s t) (m : Message)
    (live : s.lastCommitted < m.view) : Same (register s m) (register t m) := by
  unfold register
  dsimp only
  rw [same_viewAt same m.view live]
  exact same_putView same _ (by show s.lastCommitted < (viewAt t m.view).number; rw [viewAt_number]; exact live)

theorem broadcast_same {s t : State} (same : Same s t) (number : Nat) (kind : Kind)
    (value : Argument) (live : s.lastCommitted < number) :
    Same (broadcast s number kind value) (broadcast t number kind value) := by
  unfold broadcast
  dsimp only
  rw [same_self same]
  have inner := register_same same ⟨t.self, number, kind, value⟩ live
  exact congrArg (fun x : State =>
    { x with outbox := x.outbox ++ [(⟨t.self, number, kind, value⟩ : Message)] }) inner

theorem clear_same {s t : State} (same : Same s t) (number : Nat) (value : Argument)
    (live : s.lastCommitted < number) : Same (clear s number value) (clear t number value) := by
  have put : ∀ v : View, v.number = number → Same (putView s v) (putView t v) :=
    fun v at_ => same_putView same v (at_ ▸ live)
  unfold clear
  dsimp only
  rw [same_viewAt same number live]
  cases value with
  | none =>
    dsimp only
    split
    · exact same
    · exact put _ (viewAt_number t number)
  | some block =>
    dsimp only
    rw [same_validBlock same block]
    split
    · exact put _ (viewAt_number t number)
    · exact same

/-- The delivery tail of `doCommit`, with the tip it compares against named. -/
def deliverAgainst (tip : Block) (x : State) (block : Block) : State :=
  if isPrefix tip block then
    if tip == block then x else
      { x with committedTip := block, delivered := x.delivered ++ [block],
               offers := x.offers.filter fun payload => !(block.drop tip.length).contains payload }
  else if isPrefix block tip then x
  else { x with failed := true }
def deliverTip (x : State) (block : Block) : State := deliverAgainst x.committedTip x block

theorem deliverTip_same {x y : State} (same : Same x y) (block : Block) :
    Same (deliverTip x block) (deliverTip y block) := by
  unfold deliverTip
  rw [← same_committedTip same]
  unfold deliverAgainst
  repeat' split
  all_goals first
    | exact same
    | exact congrArg (fun z : State =>
        { z with committedTip := block, delivered := z.delivered ++ [block],
                 offers := z.offers.filter fun payload =>
                   !(block.drop x.committedTip.length).contains payload }) same
    | exact congrArg (fun z : State => { z with failed := true }) same

theorem doCommit_eq (s : State) (number : Nat) (block : Block) :
    doCommit s number block =
      if !validBlock s block then s else
      if (viewAt (clear s number (some block)) number).committed.isSome then
        clear s number (some block)
      else
        deliverTip
          { putView (clear s number (some block))
              { viewAt (clear s number (some block)) number with committed := some block } with
            audit := (clear s number (some block)).audit ++ [.commit s.self number block] } block := by
  have self : (clear s number (some block)).self = s.self := by
    unfold clear; dsimp only; split <;> rfl
  unfold doCommit deliverTip deliverAgainst
  dsimp only
  split
  · rfl
  · split
    · rfl
    · rw [← self]; rfl

theorem doCommit_same {s t : State} (same : Same s t) (number : Nat) (block : Block)
    (live : s.lastCommitted < number) : Same (doCommit s number block) (doCommit t number block) := by
  rw [doCommit_eq, doCommit_eq, same_validBlock same block]
  split
  · exact same
  · have cleared := clear_same same number (some block) live
    have live1 : (clear s number (some block)).lastCommitted < number := by
      rw [clear_floor]; exact live
    rw [same_viewAt cleared number live1]
    split
    · exact cleared
    · have put := same_putView cleared
        { viewAt (clear t number (some block)) number with committed := some block }
        (by show _ < (viewAt _ number).number; rw [viewAt_number]; exact live1)
      refine deliverTip_same ?_ block
      exact put

theorem raiseFloor_same {s t : State} (same : Same s t) (number : Nat) (block : Block)
    (live : s.lastCommitted < number) :
    Same (raiseFloor s number block) (raiseFloor t number block) := by
  unfold raiseFloor
  dsimp only
  rw [same_viewAt same number live, same_lastCommitted same]
  split
  · exact same_raise same number (by omega) _
  · exact same

theorem commitAt_same {s t : State} (same : Same s t) (number : Nat) (block : Block)
    (live : s.lastCommitted < number) : Same (commitAt s number block) (commitAt t number block) := by
  unfold commitAt
  exact raiseFloor_same (doCommit_same same number block live) number block
    (by rw [doCommit_floor]; exact live)

theorem sendCandidate_same {s t : State} (same : Same s t) (number : Nat) (arg : Argument)
    (live : s.lastCommitted < number) :
    Same (sendCandidate s number arg) (sendCandidate t number arg) := by
  unfold sendCandidate
  dsimp only
  rw [same_viewAt same number live]
  split
  · exact same
  · exact broadcast_same (same_putView same _
      (by show _ < (viewAt _ number).number; rw [viewAt_number]; exact live)) number .candidate arg live

theorem castVote_same {s t : State} (same : Same s t) (number : Nat) (block : Block)
    (live : s.lastCommitted < number) : Same (castVote s number block) (castVote t number block) := by
  unfold castVote
  dsimp only
  rw [same_viewAt same number live]
  split
  · exact same
  · exact broadcast_same (same_putView same _
      (by show _ < (viewAt _ number).number; rw [viewAt_number]; exact live)) number .vote (some block) live

/-! The three rules of `valueRules` and of `argumentRules`, named. -/

def voteRule (c : Config) (s : State) (number : Nat) (block : Block) : State :=
  if count (viewAt s number) .vote (some block) ≥ c.quorum && validBlock s block then
    let s := clear s number (some block)
    if (viewAt s number).sentCommit.isNone &&
        (viewAt s number).sentCandidates.all (fun a => a == some block) then
      broadcast (putView s { viewAt s number with sentCommit := some block }) number .commit (some block)
    else s
  else s
def candidateRule (c : Config) (s : State) (number : Nat) (block : Block) : State :=
  if count (viewAt s number) .vote (some block) ≥ c.faults + 1 && validBlock s block then
    sendCandidate s number (some block)
  else s
def commitRule (c : Config) (s : State) (number : Nat) (block : Block) : State :=
  if count (viewAt s number) .commit (some block) ≥ c.quorum then commitAt s number block else s

theorem valueRules_eq (c : Config) (s : State) (number : Nat) (block : Block) :
    valueRules c s number block =
      if number ≤ s.lastCommitted then s else
        commitRule c (candidateRule c (voteRule c s number block) number block) number block := by
  unfold valueRules voteRule candidateRule commitRule
  simp only [Id.run, bind, pure]
  repeat' split
  all_goals first | rfl | simp_all

theorem voteRule_floor (c : Config) (s : State) (number : Nat) (block : Block) :
    (voteRule c s number block).lastCommitted = s.lastCommitted := by
  unfold voteRule
  dsimp only
  repeat' split
  all_goals first | rfl | exact clear_floor s number (some block)
theorem candidateRule_floor (c : Config) (s : State) (number : Nat) (block : Block) :
    (candidateRule c s number block).lastCommitted = s.lastCommitted := by
  unfold candidateRule
  split
  · exact sendCandidate_floor s number (some block)
  · rfl

theorem voteRule_same {s t : State} (c : Config) (same : Same s t) (number : Nat) (block : Block)
    (live : s.lastCommitted < number) :
    Same (voteRule c s number block) (voteRule c t number block) := by
  unfold voteRule
  dsimp only
  rw [same_viewAt same number live, same_validBlock same block]
  split
  · have cleared := clear_same same number (some block) live
    have live1 : (clear s number (some block)).lastCommitted < number := by
      rw [clear_floor]; exact live
    rw [same_viewAt cleared number live1]
    split
    · exact broadcast_same (same_putView cleared _
        (by show _ < (viewAt _ number).number; rw [viewAt_number]; exact live1)) number .commit
        (some block) live1
    · exact cleared
  · exact same

theorem candidateRule_same {s t : State} (c : Config) (same : Same s t) (number : Nat)
    (block : Block) (live : s.lastCommitted < number) :
    Same (candidateRule c s number block) (candidateRule c t number block) := by
  unfold candidateRule
  rw [same_viewAt same number live, same_validBlock same block]
  split
  · exact sendCandidate_same same number (some block) live
  · exact same

theorem commitRule_same {s t : State} (c : Config) (same : Same s t) (number : Nat)
    (block : Block) (live : s.lastCommitted < number) :
    Same (commitRule c s number block) (commitRule c t number block) := by
  unfold commitRule
  rw [same_viewAt same number live]
  split
  · exact commitAt_same same number block live
  · exact same

theorem valueRules_same {s t : State} (c : Config) (same : Same s t) (number : Nat)
    (block : Block) : Same (valueRules c s number block) (valueRules c t number block) := by
  rw [valueRules_eq, valueRules_eq, same_lastCommitted same]
  split
  · exact same
  · have live : s.lastCommitted < number := by rw [same_lastCommitted same]; omega
    have voted := voteRule_same c same number block live
    have live1 : (voteRule c s number block).lastCommitted < number := by
      rw [voteRule_floor]; exact live
    have sent := candidateRule_same c voted number block live1
    exact commitRule_same c sent number block (by rw [candidateRule_floor]; exact live1)

def coreRule (c : Config) (s : State) (number : Nat) (arg : Argument) : State :=
  if count (viewAt s number) .candidate arg ≥ 2 * c.faults + 1 &&
      !(viewAt s number).sentReadyCore.contains arg then
    broadcast (putView s { viewAt s number with
      sentReadyCore := (viewAt s number).sentReadyCore ++ [arg] }) number .ready arg
  else s
def relayRule (c : Config) (s : State) (number : Nat) (arg : Argument) : State :=
  if count (viewAt s number) .ready arg ≥ c.faults + 1 &&
      !(viewAt s number).sentReadyRelay.contains arg then
    broadcast (putView s { viewAt s number with
      sentReadyRelay := (viewAt s number).sentReadyRelay ++ [arg] }) number .ready arg
  else s
def clearRule (c : Config) (s : State) (number : Nat) (arg : Argument) : State :=
  if count (viewAt s number) .ready arg ≥ 2 * c.faults + 1 then clear s number arg else s

theorem argumentRules_eq (c : Config) (s : State) (number : Nat) (arg : Argument) :
    argumentRules c s number arg =
      if number ≤ s.lastCommitted then s else
        clearRule c (relayRule c (coreRule c s number arg) number arg) number arg := by
  unfold argumentRules coreRule relayRule clearRule
  simp only [Id.run, bind, pure]
  repeat' split
  all_goals first | rfl | simp_all

theorem coreRule_floor (c : Config) (s : State) (number : Nat) (arg : Argument) :
    (coreRule c s number arg).lastCommitted = s.lastCommitted := by
  unfold coreRule; split <;> rfl
theorem relayRule_floor (c : Config) (s : State) (number : Nat) (arg : Argument) :
    (relayRule c s number arg).lastCommitted = s.lastCommitted := by
  unfold relayRule; split <;> rfl

theorem coreRule_same {s t : State} (c : Config) (same : Same s t) (number : Nat) (arg : Argument)
    (live : s.lastCommitted < number) :
    Same (coreRule c s number arg) (coreRule c t number arg) := by
  unfold coreRule
  rw [same_viewAt same number live]
  split
  · exact broadcast_same (same_putView same _
      (by show _ < (viewAt _ number).number; rw [viewAt_number]; exact live)) number .ready arg live
  · exact same

theorem relayRule_same {s t : State} (c : Config) (same : Same s t) (number : Nat) (arg : Argument)
    (live : s.lastCommitted < number) :
    Same (relayRule c s number arg) (relayRule c t number arg) := by
  unfold relayRule
  rw [same_viewAt same number live]
  split
  · exact broadcast_same (same_putView same _
      (by show _ < (viewAt _ number).number; rw [viewAt_number]; exact live)) number .ready arg live
  · exact same

theorem clearRule_same {s t : State} (c : Config) (same : Same s t) (number : Nat) (arg : Argument)
    (live : s.lastCommitted < number) :
    Same (clearRule c s number arg) (clearRule c t number arg) := by
  unfold clearRule
  rw [same_viewAt same number live]
  split
  · exact clear_same same number arg live
  · exact same

theorem argumentRules_same {s t : State} (c : Config) (same : Same s t) (number : Nat)
    (arg : Argument) : Same (argumentRules c s number arg) (argumentRules c t number arg) := by
  rw [argumentRules_eq, argumentRules_eq, same_lastCommitted same]
  split
  · exact same
  · have live : s.lastCommitted < number := by rw [same_lastCommitted same]; omega
    have core := coreRule_same c same number arg live
    have live1 : (coreRule c s number arg).lastCommitted < number := by
      rw [coreRule_floor]; exact live
    have relayed := relayRule_same c core number arg live1
    exact clearRule_same c relayed number arg (by rw [relayRule_floor]; exact live1)

/-! ## One view -/

theorem fold_same {α : Type} (f : State → α → State)
    (each : ∀ (a b : State) (item : α), Same a b → Same (f a item) (f b item))
    (items : List α) {a b : State} (same : Same a b) :
    Same (items.foldl f a) (items.foldl f b) := by
  induction items generalizing a b with
  | nil => exact same
  | cons item rest ih => exact ih (each a b item same)

theorem values_dead (c : Config) (number : Nat) (items : List Block) (s : State)
    (dead : number ≤ s.lastCommitted) :
    items.foldl (fun state block => valueRules c state number block) s = s := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    have stay : valueRules c s number item = s := by rw [valueRules_eq, if_pos dead]
    simp only [List.foldl_cons, stay, ih]

theorem arguments_dead (c : Config) (number : Nat) (items : List Argument) (s : State)
    (dead : number ≤ s.lastCommitted) :
    items.foldl (fun state arg => argumentRules c state number arg) s = s := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    have stay : argumentRules c s number item = s := by rw [argumentRules_eq, if_pos dead]
    simp only [List.foldl_cons, stay, ih]

def valuesOf (v : View) : List Block :=
  ((valuesFor v .vote ++ valuesFor v .commit).filterMap id).eraseDups
def argumentsOf (v : View) : List Argument :=
  (valuesFor v .candidate ++ valuesFor v .ready).eraseDups

theorem progressView_eq (c : Config) (s : State) (number : Nat) :
    progressView c s number =
      (argumentsOf (viewAt ((valuesOf (viewAt s number)).foldl
          (fun state block => valueRules c state number block) s) number)).foldl
        (fun state arg => argumentRules c state number arg)
        ((valuesOf (viewAt s number)).foldl (fun state block => valueRules c state number block) s) :=
  rfl

theorem progressView_same {s t : State} (c : Config) (same : Same s t) (number : Nat) :
    Same (progressView c s number) (progressView c t number) := by
  rw [progressView_eq, progressView_eq]
  have valued : Same
      ((valuesOf (viewAt s number)).foldl (fun state block => valueRules c state number block) s)
      ((valuesOf (viewAt t number)).foldl (fun state block => valueRules c state number block) t) := by
    by_cases dead : number ≤ s.lastCommitted
    · rw [values_dead c number _ s dead, values_dead c number _ t (same_lastCommitted same ▸ dead)]
      exact same
    · rw [same_viewAt same number (by omega)]
      exact fold_same _ (fun a b block ab => valueRules_same c ab number block) _ same
  generalize (valuesOf (viewAt s number)).foldl (fun state block => valueRules c state number block) s = a at valued ⊢
  generalize (valuesOf (viewAt t number)).foldl (fun state block => valueRules c state number block) t = b at valued ⊢
  by_cases dead : number ≤ a.lastCommitted
  · rw [arguments_dead c number _ a dead, arguments_dead c number _ b (same_lastCommitted valued ▸ dead)]
    exact valued
  · rw [same_viewAt valued number (by omega)]
    exact fold_same _ (fun x y arg xy => argumentRules_same c xy number arg) _ valued

/-! ## What the outer rules read -/

theorem any_agree {α : Type} (items : List α) (f g : α → Bool)
    (agree : ∀ item ∈ items, f item = g item) : items.any f = items.any g := by
  induction items with
  | nil => rfl
  | cons head rest ih =>
    simp only [List.any_cons, agree head (List.mem_cons_self ..),
      ih (fun item member => agree item (List.mem_cons_of_mem _ member))]

theorem findSome_agree {α β : Type} (items : List α) (f g : α → Option β)
    (agree : ∀ item ∈ items, f item = g item) : items.findSome? f = items.findSome? g := by
  induction items with
  | nil => rfl
  | cons head rest ih =>
    simp only [List.findSome?_cons, agree head (List.mem_cons_self ..),
      ih (fun item member => agree item (List.mem_cons_of_mem _ member))]

theorem find_agree {α : Type} (items : List α) (f g : α → Bool)
    (agree : ∀ item ∈ items, f item = g item) : items.find? f = items.find? g := by
  induction items with
  | nil => rfl
  | cons head rest ih =>
    simp only [List.find?_cons, agree head (List.mem_cons_self ..),
      ih (fun item member => agree item (List.mem_cons_of_mem _ member))]

theorem parentViews_floor (s : State) (old : Nat) (member : old ∈ parentViews s) :
    s.lastCommitted ≤ old := by
  unfold parentViews at member
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp member
  omega

theorem same_preparedAt {s t : State} (same : Same s t) (view : Nat)
    (live : s.lastCommitted ≤ view) : preparedAt s view = preparedAt t view := by
  unfold preparedAt
  split
  · rfl
  · exact congrArg View.prepared (same_viewAt_floor same view live)

theorem same_disabledAt {s t : State} (same : Same s t) (view : Nat)
    (live : s.lastCommitted ≤ view) : disabledAt s view = disabledAt t view := by
  unfold disabledAt
  split
  · rfl
  · exact congrArg View.disabled (same_viewAt_floor same view live)

theorem same_parentViews {s t : State} (same : Same s t) : parentViews s = parentViews t := by
  unfold parentViews
  rw [same_current same, same_lastCommitted same]

theorem same_isSafe {s t : State} (same : Same s t) (block : Block) :
    isSafe s block = isSafe t block := by
  unfold isSafe
  rw [same_current same]
  congr 1
  rw [← same_parentViews same]
  apply any_agree
  intro old member
  have floor := parentViews_floor s old member
  have skipped : ∀ offset, disabledAt s (old + 1 + offset) = disabledAt t (old + 1 + offset) :=
    fun offset => same_disabledAt same _ (by omega)
  simp only [same_preparedAt same old floor, skipped]

theorem same_bestParent {s t : State} (same : Same s t) : bestParent s = bestParent t := by
  unfold bestParent
  rw [← same_parentViews same]
  congr 1
  apply findSome_agree
  intro old member
  rw [same_preparedAt same old (parentViews_floor s old (List.mem_reverse.mp member))]

theorem same_bestParentView {s t : State} (same : Same s t) :
    bestParentView s = bestParentView t := by
  unfold bestParentView
  rw [← same_parentViews same, ← same_lastCommitted same]
  congr 1
  apply find_agree
  intro old member
  rw [same_preparedAt same old (parentViews_floor s old (List.mem_reverse.mp member))]

theorem same_hasWork {s t : State} (same : Same s t) : hasWork s = hasWork t := by
  unfold hasWork
  dsimp only
  rw [same_bestParent same, same_bestParentView same, same_offers same, same_current same,
    same_committedTip same]
  simp only [same_validBlock same]

/-! ## Proposal and view entry -/

def proposal (s : State) : Block :=
  bestParent s ++ [(s.offers.find? (fun bytes => validBlock s (bestParent s ++ [bytes]))).getD []]
def proposeWith (block : Block) (s : State) : State :=
  if validBlock s block then
    if (viewAt (broadcast s s.current .propose (some block))
        (broadcast s s.current .propose (some block)).current).proposal.isNone then
      putView (broadcast s s.current .propose (some block))
        { viewAt (broadcast s s.current .propose (some block))
            (broadcast s s.current .propose (some block)).current with proposal := some block }
    else broadcast s s.current .propose (some block)
  else { s with failed := true }

theorem propose_eq (s : State) :
    propose s = if !hasWork s then s else proposeWith (proposal s) s := rfl

theorem same_proposal {s t : State} (same : Same s t) : proposal s = proposal t := by
  unfold proposal
  rw [same_bestParent same, same_offers same]
  simp only [same_validBlock same]

theorem proposeWith_floor (block : Block) (s : State) :
    (proposeWith block s).lastCommitted = s.lastCommitted := by
  unfold proposeWith
  repeat' split
  all_goals rfl
theorem proposeWith_current (block : Block) (s : State) :
    (proposeWith block s).current = s.current := by
  unfold proposeWith
  repeat' split
  all_goals rfl
theorem propose_floor (s : State) : (propose s).lastCommitted = s.lastCommitted := by
  rw [propose_eq]; split
  · rfl
  · exact proposeWith_floor _ s
theorem propose_current (s : State) : (propose s).current = s.current := by
  rw [propose_eq]; split
  · rfl
  · exact proposeWith_current _ s

theorem proposeWith_same {s t : State} (same : Same s t) (block : Block)
    (live : s.lastCommitted < s.current) :
    Same (proposeWith block s) (proposeWith block t) := by
  unfold proposeWith
  rw [same_validBlock same block]
  split
  · rw [same_current same]
    have sent := broadcast_same same t.current .propose (some block) (same_current same ▸ live)
    have live1 : (broadcast s t.current .propose (some block)).lastCommitted <
        (broadcast t t.current .propose (some block)).current := same_current same ▸ live
    rw [same_current sent, same_viewAt sent _ live1]
    split
    · exact same_putView sent _ (by show _ < (viewAt _ _).number; rw [viewAt_number]; exact live1)
    · exact sent
  · exact congrArg (fun x : State => { x with failed := true }) same

theorem propose_same {s t : State} (same : Same s t) (live : s.lastCommitted < s.current) :
    Same (propose s) (propose t) := by
  rw [propose_eq, propose_eq, same_hasWork same, same_proposal same]
  split
  · exact same
  · exact proposeWith_same same _ live

def entering (c : Config) (s : State) (number : Nat) : State :=
  { s with current := number, deadline := s.now + viewTimeout c s number }

theorem enterView_eq (c : Config) (s : State) (number : Nat) :
    enterView c s number =
      if c.leader number == (putView (entering c s number) (viewAt (entering c s number) number)).self
      then propose (putView (entering c s number) (viewAt (entering c s number) number))
      else putView (entering c s number) (viewAt (entering c s number) number) := rfl

theorem enterView_floor (c : Config) (s : State) (number : Nat) :
    (enterView c s number).lastCommitted = s.lastCommitted := by
  rw [enterView_eq]; split
  · exact propose_floor _
  · rfl
theorem enterView_current (c : Config) (s : State) (number : Nat) :
    (enterView c s number).current = number := by
  rw [enterView_eq]; split
  · exact propose_current _
  · rfl

theorem enterView_same {s t : State} (c : Config) (same : Same s t) (number : Nat)
    (live : s.lastCommitted < number) : Same (enterView c s number) (enterView c t number) := by
  have entered : Same (entering c s number) (entering c t number) :=
    congrArg (fun x : State => { x with current := number, deadline := x.now + viewTimeout c x number }) same
  have live1 : (entering c s number).lastCommitted < number := live
  have placed := same_putView entered (viewAt (entering c t number) number)
    (by rw [viewAt_number]; exact live1)
  rw [enterView_eq, enterView_eq, same_viewAt entered number live1, same_self placed]
  split
  · exact propose_same placed live
  · exact placed

theorem floorJump_same {s t : State} (c : Config) (same : Same s t) :
    Same (floorJump c s) (floorJump c t) := by
  unfold floorJump
  rw [same_current same, same_lastCommitted same]
  split
  · exact enterView_same c same _ (by rw [same_lastCommitted same]; omega)
  · exact same

theorem floorJump_above (c : Config) (s : State) :
    (floorJump c s).lastCommitted < (floorJump c s).current := by
  unfold floorJump
  split
  · rw [enterView_floor, enterView_current]; omega
  · omega

/-! ## The outer rules -/

def lateRule (c : Config) (s : State) : State :=
  if c.leader s.current == s.self && (viewAt s s.current).proposal.isNone &&
      !(viewAt s s.current).disableRequested then propose s else s
def ballotRule (s : State) : State :=
  if !(viewAt s s.current).voted && !(viewAt s s.current).disableRequested then
    match (viewAt s s.current).proposal with
    | some block => if validBlock s block && isSafe s block then castVote s s.current block else s
    | none => s
  else s
def lateVote (s : State) : State :=
  if !(viewAt s s.current).voted && !(viewAt s s.current).disableRequested then
    match (viewAt s s.current).prepared.head? with
    | some block => castVote s s.current block
    | none => s
  else s
def advanceRule (c : Config) (s : State) : State :=
  if !(viewAt s s.current).prepared.isEmpty || (viewAt s s.current).disabled then
    enterView c (lateVote s) ((lateVote s).current + 1)
  else s

theorem progressOuter_eq (c : Config) (s : State) :
    progressOuter c s = advanceRule c (ballotRule (lateRule c s)) := by
  unfold progressOuter advanceRule ballotRule lateRule lateVote
  simp only [Id.run, bind, pure]
  repeat' split
  all_goals first | rfl | simp_all

theorem lateRule_floor (c : Config) (s : State) : (lateRule c s).lastCommitted = s.lastCommitted := by
  unfold lateRule; split
  · exact propose_floor s
  · rfl
theorem lateRule_current (c : Config) (s : State) : (lateRule c s).current = s.current := by
  unfold lateRule; split
  · exact propose_current s
  · rfl
theorem ballotRule_floor (s : State) : (ballotRule s).lastCommitted = s.lastCommitted := by
  unfold ballotRule
  repeat' split
  all_goals first | rfl | exact castVote_floor _ _ _
theorem ballotRule_current (s : State) : (ballotRule s).current = s.current := by
  unfold ballotRule
  repeat' split
  all_goals first | rfl | exact castVote_current _ _ _
theorem lateVote_floor (s : State) : (lateVote s).lastCommitted = s.lastCommitted := by
  unfold lateVote
  repeat' split
  all_goals first | rfl | exact castVote_floor _ _ _
theorem lateVote_current (s : State) : (lateVote s).current = s.current := by
  unfold lateVote
  repeat' split
  all_goals first | rfl | exact castVote_current _ _ _
theorem advanceRule_floor (c : Config) (s : State) :
    (advanceRule c s).lastCommitted = s.lastCommitted := by
  unfold advanceRule; split
  · rw [enterView_floor, lateVote_floor]
  · rfl
theorem advanceRule_current (c : Config) (s : State) : s.current ≤ (advanceRule c s).current := by
  unfold advanceRule; split
  · rw [enterView_current, lateVote_current]; omega
  · omega

theorem progressOuter_above (c : Config) (s : State) (live : s.lastCommitted < s.current) :
    (progressOuter c s).lastCommitted < (progressOuter c s).current := by
  rw [progressOuter_eq]
  have floor : (advanceRule c (ballotRule (lateRule c s))).lastCommitted = s.lastCommitted := by
    rw [advanceRule_floor, ballotRule_floor, lateRule_floor]
  have current := advanceRule_current c (ballotRule (lateRule c s))
  rw [ballotRule_current, lateRule_current] at current
  omega

theorem lateRule_same {s t : State} (c : Config) (same : Same s t)
    (live : s.lastCommitted < s.current) : Same (lateRule c s) (lateRule c t) := by
  unfold lateRule
  rw [same_current same, same_self same, same_viewAt same t.current (same_current same ▸ live)]
  split
  · exact propose_same same live
  · exact same

theorem ballotRule_same {s t : State} (same : Same s t) (live : s.lastCommitted < s.current) :
    Same (ballotRule s) (ballotRule t) := by
  have live1 : s.lastCommitted < t.current := same_current same ▸ live
  unfold ballotRule
  rw [same_current same, same_viewAt same t.current live1]
  simp only [same_validBlock same, same_isSafe same]
  repeat' split
  all_goals first | exact same | exact castVote_same same _ _ live1

theorem lateVote_same {s t : State} (same : Same s t) (live : s.lastCommitted < s.current) :
    Same (lateVote s) (lateVote t) := by
  have live1 : s.lastCommitted < t.current := same_current same ▸ live
  unfold lateVote
  rw [same_current same, same_viewAt same t.current live1]
  repeat' split
  all_goals first | exact same | exact castVote_same same _ _ live1

theorem advanceRule_same {s t : State} (c : Config) (same : Same s t)
    (live : s.lastCommitted < s.current) : Same (advanceRule c s) (advanceRule c t) := by
  have live1 : s.lastCommitted < t.current := same_current same ▸ live
  unfold advanceRule
  rw [lateVote_current, lateVote_current, same_current same, same_viewAt same t.current live1]
  split
  · exact enterView_same c (lateVote_same same live) _ (by rw [lateVote_floor]; omega)
  · exact same

theorem progressOuter_same {s t : State} (c : Config) (same : Same s t)
    (live : s.lastCommitted < s.current) : Same (progressOuter c s) (progressOuter c t) := by
  rw [progressOuter_eq, progressOuter_eq]
  have late := lateRule_same c same live
  have live1 : (lateRule c s).lastCommitted < (lateRule c s).current := by
    rw [lateRule_floor, lateRule_current]; exact live
  have voted := ballotRule_same late live1
  exact advanceRule_same c voted (by rw [ballotRule_floor, ballotRule_current]; exact live1)

/-! ## A pass, the pump, an input -/

theorem live_numbers (floor : Nat) (views : List View) :
    views.filterMap (fun v => if floor < v.number then some v.number else none) =
      (views.filter (fun v => floor ≤ v.number)).filterMap
        (fun v => if floor < v.number then some v.number else none) := by
  induction views with
  | nil => rfl
  | cons head rest ih =>
    by_cases keep : floor ≤ head.number
    · simp only [List.filter_cons, keep, decide_true, if_true, List.filterMap_cons, ← ih]
    · have low : ¬floor < head.number := by omega
      simp [keep, low, ih]

theorem pass_same {s t : State} (c : Config) (same : Same s t) : Same (pass c s) (pass c t) := by
  have numbers : s.views.filterMap (fun v => if s.lastCommitted < v.number then some v.number else none) =
      t.views.filterMap (fun v => if t.lastCommitted < v.number then some v.number else none) := by
    rw [live_numbers s.lastCommitted s.views, live_numbers t.lastCommitted t.views,
      ← same_lastCommitted same, same_views same]
  unfold pass
  dsimp only
  rw [numbers]
  have viewed := fold_same (fun state number => progressView c state number)
    (fun a b number ab => progressView_same c ab number)
    (t.views.filterMap (fun v => if t.lastCommitted < v.number then some v.number else none)) same
  exact progressOuter_same c (floorJump_same c viewed) (floorJump_above c _)

theorem pass_above (c : Config) (s : State) : (pass c s).lastCommitted < (pass c s).current :=
  progressOuter_above c _ (floorJump_above c _)

theorem pump_same {s t : State} (c : Config) (fuel : Nat) (same : Same s t) :
    Same (pump c fuel s) (pump c fuel t) := by
  induction fuel generalizing s t with
  | zero => exact congrArg (fun x : State => { x with needsPoll := true }) same
  | succ fuel ih =>
    have reset : Same { s with needsPoll := false } { t with needsPoll := false } :=
      congrArg (fun x : State => { x with needsPoll := false }) same
    have passed := pass_same c reset
    have stop : (forget (pass c { s with needsPoll := false }) == forget { s with needsPoll := false }) =
        (forget (pass c { t with needsPoll := false }) == forget { t with needsPoll := false }) := by
      have left : forget (pass c { s with needsPoll := false }) =
          forget (pass c { t with needsPoll := false }) := passed
      have right : forget { s with needsPoll := false } = forget { t with needsPoll := false } := reset
      rw [left, right]
    simp only [pump]
    rw [stop]
    split
    · exact passed
    · exact ih passed

theorem pump_above (c : Config) (fuel : Nat) (s : State)
    (live : 0 < fuel ∨ s.lastCommitted < s.current) :
    (pump c fuel s).lastCommitted < (pump c fuel s).current := by
  induction fuel generalizing s with
  | zero =>
    rcases live with impossible | live
    · omega
    · exact live
  | succ fuel ih =>
    simp only [pump]
    split
    · exact pass_above c _
    · exact ih _ (Or.inr (pass_above c _))

theorem serveFloor_forget (s : State) (peer : Nat) :
    forget (serveFloor s peer) = serveFloor (forget s) peer := by
  have right : serveFloor (forget s) peer =
      if peer == s.self || s.served.contains peer || s.floorEvidence.isEmpty then forget s else
        { forget s with relay := s.relay ++ s.floorEvidence.map (fun m => (peer, m)),
                        served := s.served ++ [peer] } := rfl
  rw [right]
  unfold serveFloor
  split <;> rfl

theorem serveFloor_same {s t : State} (same : Same s t) (peer : Nat) :
    Same (serveFloor s peer) (serveFloor t peer) := by
  unfold Same
  rw [serveFloor_forget s peer, serveFloor_forget t peer, same]

theorem noteAhead_same {s t : State} (same : Same s t) (sender view : Nat) :
    Same (noteAhead s sender view) (noteAhead t sender view) := by
  unfold noteAhead
  rw [← same_ahead same]
  split
  · exact same
  · exact congrArg (fun z : State =>
      { z with ahead := s.ahead.filter (fun entry : Nat × Nat => entry.1 != sender) ++ [(sender, view)] }) same

/-- What `serveViews` owes a peer: this replica's own messages from `view` on. -/
def ownFrom (c : Config) (s : State) (peer view : Nat) : List (Nat × Message) :=
  (List.range (min s.current (view + c.window) + 1 - view)).flatMap (fun offset =>
    ((viewAt s (view + offset)).received.filter fun m => m.sender == s.self).map
      fun m => (peer, m))

theorem serveViews_eq (c : Config) (s : State) (peer view : Nat) :
    serveViews c s peer view =
      if peer == s.self then s else { s with relay := s.relay ++ ownFrom c s peer view } := rfl

theorem same_ownFrom {s t : State} (c : Config) (same : Same s t) (peer view : Nat)
    (live : s.lastCommitted < view) : ownFrom c s peer view = ownFrom c t peer view := by
  unfold ownFrom
  rw [same_self same, same_current same]
  congr 1
  funext offset
  rw [same_viewAt same (view + offset) (by omega)]

theorem serveViews_same {s t : State} (c : Config) (same : Same s t) (peer view : Nat)
    (live : s.lastCommitted < view) : Same (serveViews c s peer view) (serveViews c t peer view) := by
  rw [serveViews_eq, serveViews_eq, ← same_ownFrom c same peer view live, ← same_relay same]
  have cond : (peer == t.self) = (peer == s.self) := by rw [same_self same]
  rw [cond]
  split
  · exact same
  · exact congrArg (fun z : State => { z with relay := s.relay ++ ownFrom c s peer view }) same

theorem ingest_same {s t : State} (c : Config) (same : Same s t) (m : Message) :
    Same (ingest c s m) (ingest c t m) := by
  unfold ingest
  split
  · exact same
  · rw [same_lastCommitted same]
    split
    · split
      · exact serveFloor_same same m.sender
      · exact same
    · have live : s.lastCommitted < m.view := by rw [same_lastCommitted same]; omega
      have far : horizon c s = horizon c t := by
        unfold horizon; rw [same_current same, same_lastCommitted same]
      rw [far]
      split
      · exact noteAhead_same same m.sender m.view
      · dsimp only
        rw [same_viewAt same m.view live, same_current same]
        repeat' split
        all_goals first
          | exact same
          | exact register_same same m live
          | exact serveViews_same c same m.sender m.view live
          | exact same_putView same _ (by show _ < (viewAt _ _).number; rw [viewAt_number]; exact live)

/-- The timeout part of a tick, with what it reads named. -/
def timeoutWith (c : Config) (v : View) (current self : Nat) (fire : Bool) (x : State) : State :=
  if fire then
    if !v.disableRequested then
      sendCandidate (putView { x with deadline := x.now + viewTimeout c x current }
        { v with disableRequested := true }) current none
    else if v.sentCandidates.contains none then
      { x with deadline := x.now + viewTimeout c x current,
               outbox := x.outbox ++ [(⟨self, current, .candidate, none⟩ : Message)] }
    else { x with deadline := x.now + viewTimeout c x current }
  else x
def timeoutRule (c : Config) (x : State) : State :=
  if !wantsOut c x then { x with deadline := x.now + viewTimeout c x x.current } else
  timeoutWith c (viewAt x x.current) x.current x.self (!x.needsPoll && decide (x.now ≥ x.deadline)) x

theorem same_wantsOut {s t : State} (c : Config) (same : Same s t)
    (live : s.lastCommitted < s.current) : wantsOut c s = wantsOut c t := by
  unfold wantsOut
  dsimp only
  rw [same_bestParent same, same_offers same, same_committedTip same, ← same_current same,
    same_viewAt same s.current live, same_ahead same]
  simp only [same_validBlock same]

theorem timeoutWith_same {x y : State} (c : Config) (same : Same x y) (v : View)
    (current self : Nat) (fire : Bool) (live : x.lastCommitted < current) (at_ : v.number = current) :
    Same (timeoutWith c v current self fire x) (timeoutWith c v current self fire y) := by
  have pushed : Same { x with deadline := x.now + viewTimeout c x current }
      { y with deadline := y.now + viewTimeout c y current } :=
    congrArg (fun z : State => { z with deadline := z.now + viewTimeout c z current }) same
  unfold timeoutWith
  split
  · split
    · exact sendCandidate_same (same_putView pushed _ (at_ ▸ live)) current none live
    · split
      · exact congrArg (fun z : State =>
          { z with outbox := z.outbox ++ [(⟨self, current, .candidate, none⟩ : Message)] }) pushed
      · exact pushed
  · exact same

theorem timeoutRule_same {x y : State} (c : Config) (same : Same x y)
    (live : x.lastCommitted < x.current) : Same (timeoutRule c x) (timeoutRule c y) := by
  unfold timeoutRule
  rw [← same_wantsOut c same live]
  split
  · exact congrArg (fun z : State => { z with deadline := z.now + viewTimeout c z x.current })
      same |>.trans (by rw [same_current same])
  · rw [← same_current same, ← same_self same, ← same_needsPoll same, ← same_now same,
      ← same_deadline same, ← same_viewAt same x.current live]
    exact timeoutWith_same c same _ _ _ _ live (viewAt_number x x.current)

/-- The input part of `step`, before the final pump. -/
def absorb (c : Config) (s : State) (input : Input) : State :=
  match input with
  | .delivery m => ingest c s m
  | .deliveryAt now m => ingest c { s with now := max s.now now } m
  | .checked block =>
      { s with checked := addChecked s.checked block,
               offers := match block.getLast? with
                 | some payload => if payload.isEmpty then s.offers else addOffer s payload
                 | none => s.offers }
  | .offer payload => { s with offers := addOffer s payload }
  | .poll => s
  | .tick now =>
      timeoutRule c { pump c c.pumpBudget s with now := max (pump c c.pumpBudget s).now now }

theorem step_eq (c : Config) (s : State) (input : Input) :
    step c s input =
      if !c.wellFormed || s.self ≥ c.parties || s.failed then { s with failed := true }
      else pump c c.pumpBudget (absorb c s input) := by
  unfold step absorb
  cases input <;> rfl

theorem absorb_same {s t : State} (c : Config) (same : Same s t) (input : Input)
    (budget : 0 < c.pumpBudget) : Same (absorb c s input) (absorb c t input) := by
  cases input with
  | delivery m => exact ingest_same c same m
  | deliveryAt now m =>
    exact ingest_same c (congrArg (fun x : State => { x with now := max x.now now }) same) m
  | checked block =>
    exact congrArg (fun x : State =>
      { x with checked := addChecked x.checked block,
               offers := match block.getLast? with
                 | some payload => if payload.isEmpty then x.offers else addOffer x payload
                 | none => x.offers }) same
  | offer payload =>
    exact congrArg (fun x : State => { x with offers := addOffer x payload }) same
  | poll => exact same
  | tick now =>
    have pumped := pump_same c c.pumpBudget same
    have timed : Same { pump c c.pumpBudget s with now := max (pump c c.pumpBudget s).now now }
        { pump c c.pumpBudget t with now := max (pump c c.pumpBudget t).now now } :=
      congrArg (fun x : State => { x with now := max x.now now }) pumped
    exact timeoutRule_same c timed (pump_above c c.pumpBudget s (Or.inl budget))

/-- No rule reads what `forget` drops: indistinguishable states stay indistinguishable. -/
theorem step_same {s t : State} (c : Config) (same : Same s t) (input : Input) :
    Same (step c s input) (step c t input) := by
  rw [step_eq, step_eq]
  have guard : (!c.wellFormed || decide (s.self ≥ c.parties) || s.failed) =
      (!c.wellFormed || decide (t.self ≥ c.parties) || t.failed) := by
    rw [same_self same, same_failed same]
  by_cases alive : (!c.wellFormed || decide (s.self ≥ c.parties) || s.failed) = true
  · rw [if_pos alive, if_pos (by rw [← guard]; exact alive)]
    exact congrArg (fun x : State => { x with failed := true }) same
  · rw [if_neg alive, if_neg (by rw [← guard]; exact alive)]
    have budget : 0 < c.pumpBudget := by
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, not_or, Bool.not_eq_false] at alive
      have formed := alive.1.1
      simp only [Config.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at formed
      exact formed.2
    exact pump_same c c.pumpBudget (absorb_same c same input budget)

/-- **Erasure.** A step from the forgotten state forgets to the same state. -/
theorem step_erase (c : Config) (s : State) (input : Input) :
    forget (step c s input) = forget (step c (forget s) input) :=
  step_same c (same_forget s) input

theorem liveStep_forget (c : Config) (s : State) (input : Input) :
    liveStep c (forget s) input = forget (step c s input) := (step_erase c s input).symm

/-- A replica running `liveStep` from a forgotten state is, input for input, the forgotten
image of the same replica running `step`. -/
theorem liveStep_run (c : Config) (s : State) (inputs : List Input) :
    inputs.foldl (liveStep c) (forget s) = forget (inputs.foldl (step c) s) := by
  induction inputs generalizing s with
  | nil => rfl
  | cons input rest ih => rw [List.foldl_cons, List.foldl_cons, liveStep_forget, ih]

theorem run_same {s t : State} (c : Config) (same : Same s t) (inputs : List Input) :
    Same (inputs.foldl (step c) s) (inputs.foldl (step c) t) := by
  induction inputs generalizing s t with
  | nil => exact same
  | cons input rest ih => exact ih (step_same c same input)

/-- **A rebase is unobservable** (issue #2). `Same s t` is the whole condition on a rebase
of `s` to `t`: they may differ only in the views below the floor and in the audit. Then on
every input sequence the two send the same messages, owe the same evidence, commit and
deliver the same blocks, fail together, and stay in the same view at the same floor.
`forget s` is such a rebase (`same_forget`). -/
theorem rebase_observational {s t : State} (c : Config) (same : Same s t) (inputs : List Input) :
    (inputs.foldl (step c) s).outbox = (inputs.foldl (step c) t).outbox ∧
    (inputs.foldl (step c) s).relay = (inputs.foldl (step c) t).relay ∧
    (inputs.foldl (step c) s).committedTip = (inputs.foldl (step c) t).committedTip ∧
    (inputs.foldl (step c) s).delivered = (inputs.foldl (step c) t).delivered ∧
    (inputs.foldl (step c) s).failed = (inputs.foldl (step c) t).failed ∧
    (inputs.foldl (step c) s).current = (inputs.foldl (step c) t).current ∧
    (inputs.foldl (step c) s).lastCommitted = (inputs.foldl (step c) t).lastCommitted := by
  have ran := run_same c same inputs
  exact ⟨same_outbox ran, same_relay ran, same_committedTip ran, same_delivered ran,
    same_failed ran, same_current ran, same_lastCommitted ran⟩

end Minidregg.Kernel.GenericSimplexErasure
