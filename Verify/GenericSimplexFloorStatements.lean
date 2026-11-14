import Verify.GenericSimplexJumpStarvation

/-! Statements about the commit floor (issues #2, #13; PR #18). No proofs here; each
statement names its executed satisfiable, teeth and premise witnesses, which are below.
The `Reachable`-level statements are in `Verify.GenericSimplexJumpReach`. -/
namespace Minidregg.Verify.GenericSimplexFloorStatements
open Minidregg.Kernel.GenericSimplex
open Minidregg.Verify.GenericSimplexJumpStarvation
set_option autoImplicit false

def run (c : Config) (s : State) (inputs : List Input) : State := inputs.foldl (step c) s

/-- The sends a run added to the audit. -/
def newSends (before after : State) : List Message :=
  (after.audit.drop before.audit.length).filterMap fun event =>
    match event with
    | .send m => some m
    | _ => none

/-- `lastCommitted_spec`: the maintained floor is the fold it replaces. PROVED in
`Kernel.GenericSimplexFloor` (`start_floorSpec`, `step_floorSpec`, `lastCommitted_spec`) for
every state reached from `start` by `step`. The form below quantifies over an arbitrary
prior state and is NOT the proved one: with duplicate view numbers the fold and `viewAt`
can disagree, so the proved invariant carries `CausalInvariant` (unique view numbers).

executed: `floor_agrees_executed`. teeth: `forgotten_floor_disagrees`, and
`GenericSimplexFloor.lagging_floor_refused`. -/
def FloorAgrees (s : State) : Prop := s.lastCommitted = lastCommittedView s

def LastCommittedSpec : Prop :=
  (∀ (c : Config) (self now : Nat), FloorAgrees (start c self now)) ∧
  ∀ (c : Config) (s : State) (input : Input), FloorAgrees s → FloorAgrees (step c s input)

/-- A state is clean above its floor when it is in a later view and every view strictly
below the floor has no received message. -/
def FloorClean (s : State) : Prop :=
  s.lastCommitted < s.current ∧ ∀ v ∈ s.views, v.number < s.lastCommitted → v.received = []

/-- STATEMENT `floor_refuses`. From a clean state no run sends a message for a view below
the floor it started with, and the state stays clean. (The floor view itself is kept whole
and may still act on what it had already received.)

satisfiable: `floor_refuses_executed` (the F2 late inputs and a timeout, on the kernel).
teeth: `GenericSimplexJumpStarvation.forgotten_floor_halts` (the same inputs after the
  floor is forgotten send a view-1 COMMIT below the old floor 2 and halt the replica).
premise-inhabitation: `floor_clean_executed`. -/
def FloorRefuses : Prop :=
  ∀ (c : Config) (s : State) (inputs : List Input),
    c.wellFormed = true → FloorClean s →
    FloorClean (run c s inputs) ∧ ∀ m ∈ newSends s (run c s inputs), s.lastCommitted ≤ m.view

/-- A rebase to the floor: forget every view below it. -/
def dropBelow (floor : Nat) (s : State) : State :=
  { s with views := s.views.filter fun v => decide (floor ≤ v.number) }

/-- STATEMENT `RebaseSafe`. What a rebase of `s` to `s'` at `floor` must satisfy (the answer
to issue #2). `durable` is the driver's obligation and is named, not modelled: the floor
and every view at or above it are persisted before the first send after the rebase.

satisfiable: `dropBelow_rebaseSafe_executed` (the F2 state at its floor 2).
teeth: `forgetFloor_not_rebaseSafe` (the floor is lost), `restart_above_floor_not_rebaseSafe`
  (a view above the floor is lost, with its `voted` and `sentCommit`).
premise-inhabitation: the floor is a view the F2 state really committed. -/
structure RebaseSafe (floor : Nat) (s s' : State) : Prop where
  /-- The floor is this replica's commit floor, before and after. -/
  sameFloor : s.lastCommitted = floor ∧ s'.lastCommitted = floor
  /-- It is a locally committed view and the cut is the committed tip. -/
  committed : (viewAt s floor).committed = some s.committedTip
  /-- The replica is already past the floor and stays where it was. -/
  current : floor < s.current ∧ s'.current = s.current
  /-- The floor view and every later view are untouched: `voted`, `disableRequested`,
  `sentCommit`, `sentCandidates`, the READY lists, and all received messages. -/
  kept : ∀ n, floor ≤ n → viewAt s' n = viewAt s n
  /-- Nothing below the floor survives. -/
  dropped : ∀ v ∈ s'.views, floor ≤ v.number
  /-- The retained history the safety proofs read is not dropped (`AuditExtension`). -/
  audit : s'.audit = s.audit
  rest : s'.self = s.self ∧ s'.checked = s.checked ∧ s'.offers = s.offers ∧
    s'.committedTip = s.committedTip ∧ s'.delivered = s.delivered ∧ s'.failed = s.failed

/-- STATEMENT `rebase_observational`. A safely rebased replica sends exactly what the
unrebased replica sends, on every input sequence: forgetting the views below a floor that
refuses their messages is unobservable.

satisfiable: `rebase_observational_executed`. teeth: `forgotten_floor_observable`. -/
def RebaseObservational : Prop :=
  ∀ (c : Config) (floor : Nat) (s s' : State) (inputs : List Input),
    c.wellFormed = true → FloorClean s → RebaseSafe floor s s' →
    newSends s' (run c s' inputs) = newSends s (run c s inputs)

/-! ## Witnesses, executed -/

/-- Party `p` after `[[2]]` committed in view 2 (floor 2, view 1 retired). -/
def before (party : Nat) : State := rebaseSetup.states[party]!

/-- The delayed view-1 votes of all four parties, four view-1 COMMITs, then a timeout. -/
def lateInputs : List Input :=
  ([0, 1, 2, 3].map fun p => Input.delivery ⟨p, 1, .vote, some [[1]]⟩) ++
  ([0, 1, 2, 3].map fun p => Input.delivery ⟨p, 1, .commit, some [[1]]⟩) ++ [.tick 50]

def allHonest (net : Net) (test : State → Bool) : Bool := (honestStates net).all test

theorem floor_agrees_executed :
    ([mainRun, lateVoteRun, transferred, stranded, keptMemory].all fun net =>
      allHonest net fun s => s.lastCommitted == lastCommittedView s) = true := by
  decide +kernel

theorem forgotten_floor_disagrees :
    ¬ FloorAgrees (forgetFloor 1 (before 0)) := by
  unfold FloorAgrees
  decide +kernel

theorem floor_clean_executed :
    ([0, 1, 2].all fun p =>
      let s := before p
      decide (s.lastCommitted < s.current) &&
        s.views.all fun v => !decide (v.number < s.lastCommitted) || v.received.isEmpty) = true := by
  decide +kernel

theorem floor_refuses_executed :
    ([0, 1, 2].all fun p =>
      let s := before p
      let t := run cfg s lateInputs
      !t.failed && decide (t.lastCommitted < t.current) &&
        (newSends s t).all fun m => decide (s.lastCommitted ≤ m.view)) = true := by
  decide +kernel

theorem dropBelow_rebaseSafe_executed :
    ([0, 1, 2].all fun p =>
      let s := before p
      let t := dropBelow 2 s
      s.lastCommitted == 2 && t.lastCommitted == 2 &&
        (viewAt s 2).committed == some s.committedTip && decide (2 < s.current) &&
        t.current == s.current &&
        (s.views.all fun v => decide (v.number < 2) || viewAt t v.number == viewAt s v.number) &&
        (t.views.all fun v => decide (2 ≤ v.number)) &&
        t.audit == s.audit && t.checked == s.checked && t.committedTip == s.committedTip &&
        t.delivered == s.delivered) = true := by
  decide +kernel

theorem forgetFloor_not_rebaseSafe : ¬ RebaseSafe 2 (before 0) (forgetFloor 1 (before 0)) := by
  intro safe
  have floor := safe.sameFloor.2
  revert floor
  decide +kernel

/-- With floor 1, view 2 holds party 0's `voted` and `sentCommit`; dropping it loses them. -/
theorem restart_above_floor_not_rebaseSafe :
    ¬ RebaseSafe 1 (before 0) (dropBelow 3 (before 0)) := by
  intro safe
  have view := safe.kept 2 (by decide)
  revert view
  decide +kernel

theorem rebase_observational_executed :
    ([0, 1, 2].all fun p =>
      let s := before p
      let t := dropBelow 2 s
      newSends t (run cfg t lateInputs) == newSends s (run cfg s lateInputs)) = true := by
  decide +kernel

/-- Forgetting the floor as well is observable: the forgetful replica sends a view-1 COMMIT. -/
theorem forgotten_floor_observable :
    ([0, 1, 2].all fun p =>
      let s := before p
      let t := forgetFloor 2 s
      newSends t (run cfg t lateInputs) != newSends s (run cfg s lateInputs) &&
        (newSends t (run cfg t lateInputs)).any fun m => m.view == 1 && m.kind == .commit) = true := by
  decide +kernel

#print axioms floor_agrees_executed
#print axioms forgotten_floor_disagrees
#print axioms floor_clean_executed
#print axioms floor_refuses_executed
#print axioms dropBelow_rebaseSafe_executed
#print axioms forgetFloor_not_rebaseSafe
#print axioms restart_above_floor_not_rebaseSafe
#print axioms rebase_observational_executed
#print axioms forgotten_floor_observable

end Minidregg.Verify.GenericSimplexFloorStatements
