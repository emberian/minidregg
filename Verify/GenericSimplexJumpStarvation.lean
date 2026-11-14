import Kernel.GenericSimplex

/-! Executed control for the prepared catch-up jump of PR #18 (issue #13).

The claim under test (F1): a replica that jumps past a prepared view never casts the
late vote a walker casts on leaving it (`progressOuter`, the `prepared.head?` vote),
so an adversary with one Byzantine member and one slow link can keep every view at
two honest votes, and nothing commits.

This file runs three rules on one adversary policy, n = 4, f = 1, party 3 faulty:

* `.main`       : the `step` on main (bound to it by `stepV_main`, `startV_main`);
* `.pr`         : main plus the PR's two lines at the end of `progressOuter`;
* `.prLateVote` : the PR's jump, casting the late vote in the target view first.

It imports the kernel only, so it elaborates without the proof closure. The
admission test `allowed` is `GenericSimplexObservationSafety.allowedB` restated
without `Finset` (same clauses, `poleFaulty = {3}`); it is not `runChecked` itself. -/
namespace Minidregg.Verify.GenericSimplexJumpStarvation
open Minidregg.Kernel.GenericSimplex
set_option autoImplicit false

inductive Rule where
  | main | pr | prLateVote
  deriving DecidableEq, Repr

/-- PR #18, verbatim. -/
def preparedAbove (s : State) : Nat :=
  (s.views.map View.number).foldl
    (fun acc n => if s.current < n && !(viewAt s n).prepared.isEmpty then max acc n else acc) 0

/-- What each rule appends to main's `progressOuter`. `.pr` is the PR's two lines. -/
def jumpV (rule : Rule) (c : Config) (s : State) : State :=
  match rule with
  | .main => s
  | .pr => if s.current < preparedAbove s then enterView c s (preparedAbove s + 1) else s
  | .prLateVote =>
      if s.current < preparedAbove s then
        let j := preparedAbove s
        let v := viewAt s j
        let voted :=
          if !v.voted && !v.disableRequested then
            match v.prepared.head? with
            | some block => castVote s j block
            | none => s
          else s
        enterView c voted (j + 1)
      else s

/-- `pass` ends in `progressOuter`, and the PR's lines are the last thing in it. -/
def passV (rule : Rule) (c : Config) (s : State) : State := jumpV rule c (pass c s)

def pumpV (rule : Rule) (c : Config) : Nat → State → State
  | 0, s => { s with needsPoll := true }
  | fuel + 1, s =>
      let s := { s with needsPoll := false }
      let next := passV rule c s
      if next == s then next else pumpV rule c fuel next

/-- `step`, with `pump` replaced by `pumpV rule`. -/
def stepV (rule : Rule) (c : Config) (s : State) (input : Input) : State :=
  if !c.wellFormed || s.self ≥ c.parties || s.failed then { s with failed := true } else
  let next := match input with
    | .delivery m => ingest c s m
    | .deliveryAt now m => ingest c {s with now := max s.now now} m
    | .checked block =>
        let offers := match block.getLast? with
          | some payload => if payload.isEmpty then s.offers else addUnique s.offers payload
          | none => s.offers
        { s with checked := addUnique s.checked block, offers := offers }
    | .offer payload => { s with offers := addUnique s.offers payload }
    | .poll => s
    | .tick now =>
        let s := pumpV rule c c.pumpBudget s
        let s := { s with now := max s.now now }
        let v := viewAt s s.current
        if !s.needsPoll && s.now ≥ s.deadline && !v.disableRequested then
          sendCandidate (putView s { v with disableRequested := true }) s.current none
        else s
  pumpV rule c c.pumpBudget next

def startV (rule : Rule) (c : Config) (self now : Nat) : State :=
  if !c.wellFormed || self ≥ c.parties then
    { self := self, now := now, deadline := now, failed := true }
  else
    pumpV rule c c.pumpBudget (enterView c
      { self := self, now := now, deadline := now + c.timeout } 1)

theorem pumpV_main (c : Config) (fuel : Nat) (s : State) :
    pumpV .main c fuel s = pump c fuel s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    rw [pumpV, pump]
    simp only [passV, jumpV, ih]

theorem pumpV_main_fun : pumpV .main = pump := by
  funext c fuel s
  exact pumpV_main c fuel s

/-- The `.main` rule IS the kernel's `step`. -/
theorem stepV_main (c : Config) (s : State) (input : Input) :
    stepV .main c s input = step c s input := by
  unfold stepV step
  rw [pumpV_main_fun]
  cases input <;> rfl

theorem startV_main (c : Config) (self now : Nat) :
    startV .main c self now = start c self now := by
  unfold startV start
  rw [pumpV_main_fun]

/-! ## The network and the admission test -/

def cfg : Config := { parties := 4, faults := 1, timeout := 1 }

structure Net where
  states : Array State
  /-- (receiver, message) pairs already delivered. -/
  seen : List (Nat × Message) := []
  /-- The inputs applied, newest first. -/
  traceRev : List (Nat × Input) := []
  /-- False once an input `allowed` refuses was attempted. -/
  ok : Bool := true

def initial (rule : Rule) : Net :=
  { states := #[startV rule cfg 0 0, startV rule cfg 1 0, startV rule cfg 2 0, startV rule cfg 3 0] }

/-- `allowedB cfg {3}`: an honest receiver; a delivery is from an enrolled sender and,
when the sender is honest, is a message that sender really sent (its audit holds it). -/
def allowed (net : Net) (receiver : Nat) (input : Input) : Bool :=
  decide (receiver < cfg.parties) && receiver != 3 &&
  match input with
  | .delivery m | .deliveryAt _ m =>
      decide (m.sender < cfg.parties) &&
        (m.sender == 3 || (net.states[m.sender]!).audit.contains (.send m))
  | .tick _ | .checked _ | .offer _ | .poll => true

def advanceV (rule : Rule) (net : Net) (receiver : Nat) (input : Input) : Net :=
  if !net.ok || !allowed net receiver input then { net with ok := false } else
  { net with
    states := net.states.set! receiver (stepV rule cfg net.states[receiver]! input)
    traceRev := (receiver, input) :: net.traceRev
    seen := match input with
      | .delivery m => (receiver, m) :: net.seen
      | _ => net.seen }

/-- Replay of a concrete input list, refusing at the first inadmissible input. -/
def runV (rule : Rule) (schedule : List (Nat × Input)) : Net :=
  schedule.foldl (fun net (receiver, input) => advanceV rule net receiver input) (initial rule)

/-! ## The adversary policy

Blocks are `blk w = [[1],[2],…,[w]]`; every honest party is source-checked on all of
them up front. Honest parties are 0, 1, 2. Party 0 is never lagged. In round `w ≥ 2`
the victim is party 2 (even `w`) or party 1 (odd `w`).

Byzantine party 3 in round `w`: VOTE, CANDIDATE, READY for `blk w` to the victim;
CANDIDATE, READY to party 0; nothing to the third party; the PROPOSE when it leads.
It never sends COMMIT.

Network: every honest message is delivered, except that the link between 1 and 2
runs one round late (in round `w` it holds messages for views `≥ w-1`), and party 0's
view-1 messages reach party 2 only in round 3. No tick is ever delivered. -/

def blk (w : Nat) : Block := (List.range w).map fun i => [UInt8.ofNat (i + 1)]

def victim (w : Nat) : Nat := if w % 2 == 0 then 2 else 1

def byz (receiver view : Nat) (kind : Kind) : Nat × Input :=
  (receiver, .delivery ⟨3, view, kind, some (blk view)⟩)

def byzRound (w : Nat) : List (Nat × Input) :=
  if w == 1 then
    [byz 0 1 .candidate, byz 0 1 .ready, byz 1 1 .candidate, byz 1 1 .ready]
  else
    (if cfg.leader w == 3 then [byz 0 w .propose, byz (3 - victim w) w .propose] else []) ++
    [byz (victim w) w .vote, byz (victim w) w .candidate, byz (victim w) w .ready,
     byz 0 w .candidate, byz 0 w .ready]

def held (round sender receiver : Nat) (m : Message) : Bool :=
  ((sender == 1 && receiver == 2) || (sender == 2 && receiver == 1)) && decide (m.view + 1 ≥ round) ||
  (sender == 0 && receiver == 2 && m.view == 1 && decide (round ≤ 2))

/-- Every honest send not yet delivered to an honest peer and not held. -/
def pending (net : Net) (hold : Nat → Nat → Message → Bool) : List (Nat × Message) :=
  [0, 1, 2].flatMap fun sender =>
    (net.states[sender]!).audit.flatMap fun event =>
      match event with
      | .send m =>
          [0, 1, 2].filterMap fun receiver =>
            if receiver != sender && !net.seen.contains (receiver, m) && !hold sender receiver m
            then some (receiver, m) else none
      | _ => []

def settle (rule : Rule) (hold : Nat → Nat → Message → Bool) : Nat → Net → Net
  | 0, net => { net with ok := false }
  | fuel + 1, net =>
      match pending net hold with
      | [] => net
      | batch => settle rule hold fuel
          (batch.foldl (fun n (receiver, m) =>
            if n.seen.contains (receiver, m) then n else advanceV rule n receiver (.delivery m)) net)

def playRound (rule : Rule) (net : Net) (w : Nat) : Net :=
  settle rule (held w) 64 ((byzRound w).foldl (fun n (receiver, input) => advanceV rule n receiver input) net)

def checks (rounds : Nat) : List (Nat × Input) :=
  [0, 1, 2].flatMap fun party =>
    (List.range (rounds + 2)).map fun i => (party, .checked (blk (i + 1)))

/-- The adversary policy played for `rounds` rounds from the real start. -/
def play (rule : Rule) (rounds : Nat) : Net :=
  (List.range rounds).foldl (fun net i => playRound rule net (i + 1))
    ((checks rounds).foldl (fun n (receiver, input) => advanceV rule n receiver input) (initial rule))

def Net.schedule (net : Net) : List (Nat × Input) := net.traceRev.reverse

/-! ## Observations -/

def honestStates (net : Net) : List State := [0, 1, 2].map fun p => net.states[p]!

def anyDelivered (net : Net) : Bool := (honestStates net).any fun s => !s.delivered.isEmpty

def anyCommitted (net : Net) : Bool :=
  (honestStates net).any fun s => s.views.any fun v => v.committed.isSome

def anyFailed (net : Net) : Bool := (honestStates net).any (·.failed)

def sentBy (net : Net) (view : Nat) (kind : Kind) : List Nat :=
  [0, 1, 2].filter fun p =>
    (net.states[p]!).audit.any fun event =>
      match event with
      | .send m => m.view == view && m.kind == kind && m.sender == p
      | _ => false

def currents (net : Net) : List Nat := (honestStates net).map (·.current)

/-- Honest messages still undelivered at the end, as (sender, receiver, view). -/
def undelivered (net : Net) : List (Nat × Nat × Nat) :=
  (pending net fun _ _ _ => false).map fun (receiver, m) => (m.sender, receiver, m.view)

/-- The views of the honest messages still undelivered. -/
def undeliveredViews (net : Net) : List Nat := ((undelivered net).map fun (_, _, view) => view).eraseDups

def report (net : Net) (rounds : Nat) : String :=
  s!"ok={net.ok} inputs={net.traceRev.length} currents={currents net} " ++
  s!"delivered={(honestStates net).map (·.delivered.length)} failed={anyFailed net}\n" ++
  String.intercalate "\n" ((List.range rounds).map fun i =>
    let w := i + 1
    s!"  view {w}: votes={sentBy net w .vote} commits={sentBy net w .commit} " ++
    s!"prepared={(honestStates net).map fun s => (viewAt s w).prepared.length} " ++
    s!"committed={(honestStates net).map fun s => (viewAt s w).committed.isSome}")

/-! ## F1, executed: twelve rounds, three leader rotations

`#guard` evaluates the compiled definitions at elaboration and fails the file if false. -/

def rounds : Nat := 12
def prRun : Net := play .pr rounds
def mainRun : Net := play .main rounds
def lateVoteRun : Net := play .prLateVote rounds

-- (a) every input of each run passed `allowed`, and the PR run's concrete input list
-- replays to the same states.
#guard prRun.ok && mainRun.ok && lateVoteRun.ok
#guard prRun.schedule.length == 330
#guard (runV .pr prRun.schedule).ok && (runV .pr prRun.schedule).states == prRun.states

-- (b) under the PR's rule: nothing delivered, nothing committed, nobody failed, and the
-- views kept advancing (no tick was delivered: every view ended prepared).
#guard !anyDelivered prRun && !anyCommitted prRun && !anyFailed prRun
#guard currents prRun == [13, 12, 13]
-- Every view has exactly two honest VOTEs.
#guard (List.range rounds).all fun i => (sentBy prRun (i + 1) .vote).length == 2
-- Views 2..10 hold exactly one honest COMMIT (the jumper's, once the slow link delivers);
-- views 1, 11, 12 hold none. Party 3 sends none. Three are needed.
#guard (List.range 9).all fun i => (sentBy prRun (i + 2) .commit).length == 1
#guard [1, 11, 12].all fun w => (sentBy prRun w .commit).isEmpty
-- Fairness of the finite run: the only honest messages not yet delivered are for the last
-- two views (the one-round lag on the 1-2 link).
#guard (undeliveredViews prRun).all fun view => decide (view ≥ rounds - 1)

-- (c) main's `step` under the same adversary policy commits views 1..10 at all three.
#guard (honestStates mainRun).all fun s => s.delivered.length == 10
#guard (List.range 10).all fun i =>
  (honestStates mainRun).all fun s => (viewAt s (i + 1)).committed.isSome
#guard !anyFailed mainRun
-- The PR run's literal input list is not admitted under main: it delivers messages only
-- the jumping replicas sent. The comparison is therefore by policy, not by input list.
#guard !(runV .main prRun.schedule).ok

-- Repair: the jump casts the late vote in its target view. Same policy: views 2..10 commit.
#guard (honestStates lateVoteRun).all fun s => s.delivered.length == 9
#guard (List.range 9).all fun i =>
  (honestStates lateVoteRun).all fun s => (viewAt s (i + 2)).committed.isSome
#guard !anyFailed lateVoteRun

/-! ## F2, executed: a floorless rebase halts every honest replica

Rule `.main` throughout (the kernel's `step`). `dropViews v` is OUR model of the rebase
asked about in issue #2 ("views ≤ v collapse"): it forgets those views and nothing else,
and `ingest` still accepts their messages.

View 1: party 0 proposes `[[1]]`, all three vote, the votes are delayed. All three time
out, send CANDIDATE(⊥), and view 1 is disabled. View 2: party 1 proposes `[[2]]`, which
commits at all three. Then the rebase at 2, then the delayed view-1 votes and one
Byzantine vote. Each rebased replica has forgotten its CANDIDATE(⊥) and sends COMMIT. -/

def dropViews (v : Nat) (s : State) : State :=
  { s with views := s.views.filter fun view => decide (view.number > v) }

def holdViewOneVotes (_ _ : Nat) (m : Message) : Bool := m.view == 1 && m.kind == .vote

def rebaseSetup : Net :=
  let inputs : List (Nat × Input) :=
    [(1, .offer [2]), (1, .checked [[2]]), (1, .checked [[1]]),
     (0, .checked [[1]]), (0, .checked [[2]]), (2, .checked [[1]]), (2, .checked [[2]])]
  let net := inputs.foldl (fun n (receiver, input) => advanceV .main n receiver input) (initial .main)
  let net := settle .main holdViewOneVotes 64 net
  let net := [0, 1, 2].foldl (fun n party => advanceV .main n party (.tick 5)) net
  settle .main holdViewOneVotes 64 net

def lateVotes (net : Net) : Net :=
  let net := [0, 1, 2].foldl
    (fun n party => advanceV .main n party (.delivery ⟨3, 1, .vote, some [[1]]⟩)) net
  let net := settle .main (fun _ _ _ => false) 64 net
  -- One Byzantine COMMIT, so that two forgetful replicas are enough.
  let net := [0, 1, 2].foldl
    (fun n party => advanceV .main n party (.delivery ⟨3, 1, .commit, some [[1]]⟩)) net
  settle .main (fun _ _ _ => false) 64 net

def rebased (parties : List Nat) (net : Net) : Net :=
  { net with states := parties.foldl (fun states p => states.set! p (dropViews 2 states[p]!)) net.states }

def noRebase : Net := lateVotes rebaseSetup
def rebaseAll : Net := lateVotes (rebased [0, 1, 2] rebaseSetup)
def rebaseTwo : Net := lateVotes (rebased [0, 1] rebaseSetup)

-- Before the rebase: view 1 disabled, `[[2]]` committed in view 2 at all three, all healthy.
#guard rebaseSetup.ok && !anyFailed rebaseSetup
#guard (honestStates rebaseSetup).all fun s =>
  (viewAt s 1).disabled && (viewAt s 2).committed == some [[2]] && s.committedTip == [[2]]
-- Control, no rebase: the late votes arrive, nobody sends COMMIT in view 1, nobody fails.
#guard noRebase.ok && !anyFailed noRebase && (sentBy noRebase 1 .commit).isEmpty
-- All three rebase: all three send COMMIT for `[[1]]` in view 1 and all three halt.
#guard rebaseAll.ok && sentBy rebaseAll 1 .commit == [0, 1, 2]
#guard (honestStates rebaseAll).all (·.failed)
-- Two rebase (f+1): they send COMMIT; with the Byzantine COMMIT all three halt, including
-- the replica that kept its memory.
#guard rebaseTwo.ok && sentBy rebaseTwo 1 .commit == [0, 1]
#guard (honestStates rebaseTwo).all (·.failed)
-- The halted replicas recorded the conflicting commit before halting.
#guard (honestStates rebaseAll).all fun s =>
  s.audit.contains (.commit s.self 1 [[1]]) && s.audit.contains (.commit s.self 2 [[2]])

/-! ## The same facts as kernel-checked theorems (`decide +kernel`, standard axioms only) -/

/-- F1. Under the PR's rule the adversary policy is admitted for twelve rounds (three leader
rotations), the honest replicas reach views 13, 12, 13, every view has exactly two honest
VOTEs and at most one honest COMMIT, and no honest replica commits or delivers anything. -/
theorem pr_jump_starves_commit :
    prRun.ok = true ∧ currents prRun = [13, 12, 13] ∧
    anyDelivered prRun = false ∧ anyCommitted prRun = false ∧ anyFailed prRun = false ∧
    ((List.range rounds).all fun i => (sentBy prRun (i + 1) .vote).length == 2) = true ∧
    ((List.range rounds).all fun i => decide ((sentBy prRun (i + 1) .commit).length ≤ 1)) = true ∧
    ((undeliveredViews prRun).all fun view => decide (view ≥ rounds - 1)) = true := by
  decide +kernel

/-- Control. Main's `step` (`stepV_main`) under the same policy commits views 1..10 at all
three honest replicas. -/
theorem main_commits_same_policy :
    mainRun.ok = true ∧ anyFailed mainRun = false ∧
    ((List.range 10).all fun i =>
      (honestStates mainRun).all fun s => (viewAt s (i + 1)).committed.isSome) = true := by
  decide +kernel

/-- Repair. The jump that first casts the late vote in its target view commits views 2..10
under the same policy. This is one schedule, not a progress theorem. -/
theorem late_vote_jump_commits_same_policy :
    lateVoteRun.ok = true ∧ anyFailed lateVoteRun = false ∧
    ((List.range 9).all fun i =>
      (honestStates lateVoteRun).all fun s => (viewAt s (i + 2)).committed.isSome) = true := by
  decide +kernel

/-- F2. Without the rebase nobody sends a view-1 COMMIT and nobody fails; with it (all three,
or only two plus one Byzantine COMMIT) every honest replica ends `failed`. -/
theorem floorless_rebase_halts :
    (noRebase.ok = true ∧ anyFailed noRebase = false ∧ sentBy noRebase 1 .commit = []) ∧
    (rebaseAll.ok = true ∧ sentBy rebaseAll 1 .commit = [0, 1, 2] ∧
      (honestStates rebaseAll).all (·.failed) = true) ∧
    (rebaseTwo.ok = true ∧ sentBy rebaseTwo 1 .commit = [0, 1] ∧
      (honestStates rebaseTwo).all (·.failed) = true) := by
  decide +kernel

#print axioms pr_jump_starves_commit
#print axioms main_commits_same_policy
#print axioms late_vote_jump_commits_same_policy
#print axioms floorless_rebase_halts

end Minidregg.Verify.GenericSimplexJumpStarvation
