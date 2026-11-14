import Verify.GenericSimplexJumpStarvation

/-! Statements for the commit-floor takeover (issues #2, #13; PR #18). No proofs.

`stepF` and `rebaseAt` are CANDIDATE definitions that exist so the Props can be written
and their witnesses executed; the kernel has no floor yet. `Reachable`-level statements
(`settled_below_frontier`) need `Kernel.GeneralSimplexReachability` and are not here. -/
namespace Minidregg.Verify.GenericSimplexFloorStatements
open Minidregg.Kernel.GenericSimplex
open Minidregg.Verify.GenericSimplexJumpStarvation
set_option autoImplicit false

/-- Candidate message floor at the ingress boundary: a delivery for a view at or below
the floor is treated as no input. Everything else is the kernel's `step`. -/
def stepF (floor : Nat) (c : Config) (s : State) (input : Input) : State :=
  match input with
  | .delivery m | .deliveryAt _ m => if m.view ≤ floor then s else step c s input
  | _ => step c s input

def runF (floor : Nat) (c : Config) (s : State) (inputs : List Input) : State :=
  inputs.foldl (stepF floor c) s

/-- The sends a run added to the audit. -/
def newSends (before after : State) : List Message :=
  (after.audit.drop before.audit.length).filterMap fun event =>
    match event with
    | .send m => some m
    | _ => none

/-- A state is above the floor when it is in a later view and holds no view below the
floor. The floor view itself stays: `isSafe` and `bestParent` read its prepared block. -/
def AboveFloor (floor : Nat) (s : State) : Prop :=
  floor < s.current ∧ ∀ v ∈ s.views, floor ≤ v.number

/-- A floor view that can never act again: it has no received messages, so no VOTE,
CANDIDATE, READY or COMMIT threshold is met in it. -/
def FloorQuiet (floor : Nat) (s : State) : Prop := (viewAt s floor).received = []

/-- STATEMENT `floor_refuses`. From a state above its floor whose floor view is quiet,
no run of `stepF` ever sends a message for a view at or below the floor, and the state
stays above the floor with the floor view quiet.

satisfiable: `floored_rebase_is_silent` below (the F2 inputs against a floored rebase).
teeth: `GenericSimplexJumpStarvation.floorless_rebase_halts` (the same inputs through
  `step` on a floorless rebase send COMMIT in view 1 and halt all three replicas).
premise-inhabitation: `rebased_state_above_floor` below. -/
def FloorRefuses : Prop :=
  ∀ (c : Config) (floor : Nat) (s : State) (inputs : List Input),
    c.wellFormed = true → AboveFloor floor s → FloorQuiet floor s →
    AboveFloor floor (runF floor c s inputs) ∧ FloorQuiet floor (runF floor c s inputs) ∧
    ∀ m ∈ newSends s (runF floor c s inputs), floor < m.view

/-- Candidate rebase: forget every view below `floor`, and reduce the floor view to its
committed block. The audit, the checks, the offers, the tip and every later view stay. -/
def rebaseAt (floor : Nat) (s : State) : State :=
  { s with views :=
      (s.views.filter fun v => decide (v.number > floor)) ++
        [{ number := floor, prepared := [s.committedTip], committed := some s.committedTip }] }

/-- STATEMENT `RebaseSafe`. What a rebase of `s` to `s'` at view `floor` must satisfy.
`durable` is the driver's obligation and is named, not modelled: the floor is persisted
before the first send after the rebase.

satisfiable: `rebaseAt_is_rebaseSafe_witness` below (the F2 state at floor 2).
teeth: `dropViews_not_rebaseSafe` below (the floorless model keeps no floor view), and
  `restart_above_floor_not_rebaseSafe` (forgetting a view above the floor).
premise-inhabitation: `floor` is a view the F2 state really committed. -/
structure RebaseSafe (floor : Nat) (s s' : State) : Prop where
  /-- The floor is a locally committed view and the cut is the committed tip. -/
  committed : (viewAt s floor).committed = some s.committedTip
  /-- The replica is already past the floor and stays where it was. -/
  current : floor < s.current ∧ s'.current = s.current
  /-- Every later view is untouched: `voted`, `disableRequested`, `sentCommit`,
  `sentCandidates`, `sentReadyCore`, `sentReadyRelay`, and all received messages. -/
  aboveKept : ∀ n, floor < n → viewAt s' n = viewAt s n
  /-- Nothing below the floor survives, and the floor view is the committed block alone. -/
  aboveFloor : ∀ v ∈ s'.views, floor ≤ v.number
  floorView : viewAt s' floor =
    { number := floor, prepared := [s.committedTip], committed := some s.committedTip }
  /-- The retained history the safety proofs read is not dropped (`AuditExtension`). -/
  audit : s'.audit = s.audit
  rest : s'.self = s.self ∧ s'.checked = s.checked ∧ s'.offers = s.offers ∧
    s'.committedTip = s.committedTip ∧ s'.delivered = s.delivered ∧ s'.failed = s.failed

/-- STATEMENT `rebase_sends_as_unrebased`. The safety consequence wanted from `RebaseSafe`:
after a safe rebase, under the floored step, the replica is silent at and below the floor.
(Together with `aboveKept` this is what keeps `voteOnce` and `commitCandidateLock` true of
the combined send trace: later views are bit-identical, earlier views are silent.) -/
def RebaseSilent : Prop :=
  ∀ (c : Config) (floor : Nat) (s s' : State) (inputs : List Input),
    c.wellFormed = true → RebaseSafe floor s s' →
    ∀ m ∈ newSends s' (runF floor c s' inputs), floor < m.view

/-! ## Witnesses, executed on the F2 state (after `[[2]]` committed in view 2) -/

def before (party : Nat) : State := rebaseSetup.states[party]!

/-- The delayed view-1 votes of all four parties, then four view-1 COMMITs. -/
def lateInputs : List Input :=
  ([0, 1, 2, 3].map fun p => Input.delivery ⟨p, 1, .vote, some [[1]]⟩) ++
  ([0, 1, 2, 3].map fun p => Input.delivery ⟨p, 1, .commit, some [[1]]⟩)

/-- Satisfiable: the floored rebase ignores the late inputs: no send, no failure, state unchanged. -/
theorem floored_rebase_is_silent :
    ([0, 1, 2].all fun p =>
      let s := rebaseAt 2 (before p)
      let t := runF 2 cfg s lateInputs
      t == s && !t.failed && (newSends s t).isEmpty) = true := by
  decide +kernel

/-- Teeth: the same inputs through the kernel's `step` on the floorless rebase make every
replica send a view-1 COMMIT and fail. -/
theorem floorless_rebase_is_not_silent :
    ([0, 1, 2].all fun p =>
      let s := dropViews 2 (before p)
      let t := lateInputs.foldl (step cfg) s
      t.failed && (newSends s t).any fun m => m.view == 1 && m.kind == .commit) = true := by
  decide +kernel

/-- Premise inhabitation for `FloorRefuses`. -/
theorem rebased_state_above_floor :
    ([0, 1, 2].all fun p =>
      let s := rebaseAt 2 (before p)
      decide (2 < s.current) && (s.views.all fun v => decide (2 ≤ v.number)) &&
        (viewAt s 2).received.isEmpty) = true := by
  decide +kernel

/-- The executable content of `RebaseSafe 2 (before p) (rebaseAt 2 (before p))` on the views
the state holds: the floor is committed with the tip, later views are equal, nothing below
survives, the floor view is the committed block alone, and the rest is unchanged. -/
theorem rebaseAt_is_rebaseSafe_witness :
    ([0, 1, 2].all fun p =>
      let s := before p
      let t := rebaseAt 2 s
      (viewAt s 2).committed == some s.committedTip && decide (2 < s.current) &&
        t.current == s.current &&
        (s.views.all fun v => decide (v.number ≤ 2) || viewAt t v.number == viewAt s v.number) &&
        (t.views.all fun v => decide (2 ≤ v.number)) &&
        viewAt t 2 == { number := 2, prepared := [s.committedTip], committed := some s.committedTip } &&
        t.audit == s.audit && t.checked == s.checked && t.committedTip == s.committedTip &&
        t.delivered == s.delivered) = true := by
  decide +kernel

/-- Teeth: the floorless model is not a safe rebase: it keeps no floor view. -/
theorem dropViews_not_rebaseSafe : ¬ RebaseSafe 2 (before 0) (dropViews 2 (before 0)) := by
  intro safe
  have view := safe.floorView
  revert view
  decide +kernel

/-- Teeth: a restart that forgets a view above its floor is not a safe rebase. With floor 1,
view 2 holds party 0's `voted` and `sentCommit`; dropping it loses them. -/
theorem restart_above_floor_not_rebaseSafe :
    ¬ RebaseSafe 1 (before 0) (dropViews 2 (before 0)) := by
  intro safe
  have view := safe.aboveKept 2 (by decide)
  revert view
  decide +kernel

#print axioms floored_rebase_is_silent
#print axioms floorless_rebase_is_not_silent
#print axioms rebased_state_above_floor
#print axioms rebaseAt_is_rebaseSafe_witness
#print axioms dropViews_not_rebaseSafe
#print axioms restart_above_floor_not_rebaseSafe

end Minidregg.Verify.GenericSimplexFloorStatements
