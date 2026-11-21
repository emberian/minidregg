import Kernel.GenericSimplex

/-! Executed controls for the agreement engine: a view jump that starves commit (F1), a
forgotten floor (F2), a replica stranded behind a peer's floor (F3). n = 4, f = 1, party 3 faulty.

F1 is the negative control for any catch-up jump: a replica that jumps past a prepared view
(PR #18's rule, `.pr`) never casts the late vote a walker casts on leaving it, so one
Byzantine member and one slow link keep every view at two honest votes and nothing commits.
The kernel's `step` (`.main`, bound by `stepV_main`, `startV_main`) commits under the same
policy, and so does the jump that casts the late vote first (`.prLateVote`).

Why F1 was once thought gone. Between 788dfb51f and aac9eba60 this policy stopped starving
`.pr`, and the two F1 theorems were removed. The step was not the reason. The network here
had learned to forward a message that appears a second time in a party's outbox (the
repeated CANDIDATE(⊥) of a stuck replica) and forwarded it past the policy's slow link.
An honest replica then sent each READY twice (once by the `2f+1` CANDIDATE rule, once by
the `f+1` READY rule), so every held READY leaked through and the lagged party voted. With
repeats held like any other message (`repeated`) the policy starves `.pr` exactly as
before. The kernel now sends READY for one argument once; the schedule did not depend on
the duplicate, and every fact below holds unchanged without it.

The facts are theorems by compiled evaluation (`native_decide`): each run is evaluated once,
in well under a second. A run of twelve rounds costs the kernel's reduction about half a
minute, and these are executed controls of a schedule, where the kernel is not the point;
`Verify/GenericSimplexJumpReach.lean` pins each with `#assert_compiled` and carries the
kernel-checked reachable witness on a short run (`reachRun`).

It imports the kernel only, so it elaborates without the proof closure. The admission test
`allowed` is `GenericSimplexObservationSafety.allowedB` restated without `Finset` (same
clauses, `poleFaulty = {3}`; tied to it in `Verify/GenericSimplexJumpReach.lean`). -/
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
      if forget next == forget s then next else pumpV rule c fuel next

/-- `step`, with `pump` replaced by `pumpV rule`. -/
def stepV (rule : Rule) (c : Config) (s : State) (input : Input) : State :=
  if !c.wellFormed || s.self ≥ c.parties || s.failed then { s with failed := true } else
  let next := match input with
    | .delivery m => ingest c s m
    | .deliveryAt now m => ingest c {s with now := max s.now now} m
    | .checked block =>
        let offers := match block.getLast? with
          | some payload => if payload.isEmpty then s.offers else addOffer s payload
          | none => s.offers
        { s with checked := addChecked s.checked block, offers := offers }
    | .offer payload => { s with offers := addOffer s payload }
    | .poll => s
    | .tick now =>
        let s := pumpV rule c c.pumpBudget s
        let s := { s with now := max s.now now }
        if !wantsOut c s then { s with deadline := s.now + viewTimeout c s s.current } else
        if !s.needsPoll && s.now ≥ s.deadline then
          let s := { s with deadline := s.now + viewTimeout c s s.current }
          let v := viewAt s s.current
          if !v.disableRequested then
            sendCandidate (putView s { v with disableRequested := true }) s.current none
          else if v.sentCandidates.contains none then
            { s with outbox := s.outbox ++ [⟨s.self, s.current, .candidate, none⟩] }
          else s
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
  /-- Per party, how much of its outbox the network has scanned for repeats. -/
  scanned : List Nat := [0, 0, 0, 0]
  /-- Control: a network that never forwards floor evidence. -/
  relayOff : Bool := false

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

/-- Floor evidence an honest party owes an honest peer (`State.relay`), not yet delivered. -/
def owed (net : Net) : List (Nat × Message) :=
  if net.relayOff then [] else
  [0, 1, 2].flatMap fun relayer =>
    (net.states[relayer]!).relay.filter fun (receiver, m) =>
      decide (receiver < 3) && receiver != relayer && !net.seen.contains (receiver, m)

/-- Messages an honest party put in its outbox again since the last scan (the repeated
CANDIDATE(⊥) of a stuck replica): each goes to both
other honest parties once more, unless the policy holds it. -/
def repeated (net : Net) (hold : Nat → Nat → Message → Bool) : List (Nat × Message) :=
  [0, 1, 2].flatMap fun sender =>
    let box := (net.states[sender]!).outbox
    let start := net.scanned[sender]!
    (List.range (box.length - start)).flatMap fun k =>
      let m := box[start + k]!
      if (box.take (start + k)).contains m then
        [0, 1, 2].filterMap fun receiver =>
          if receiver != sender && !hold sender receiver m then some (receiver, m) else none
      else []

def settle (rule : Rule) (hold : Nat → Nat → Message → Bool) : Nat → Net → Net
  | 0, net => { net with ok := false }
  | fuel + 1, net =>
      let again := repeated net hold
      let net := { net with scanned := (List.range 4).map fun p => (net.states[p]!).outbox.length }
      match again, pending net hold ++ owed net with
      | [], [] => net
      | again, batch => settle rule hold fuel
          (batch.foldl (fun n (receiver, m) =>
            if n.seen.contains (receiver, m) then n else advanceV rule n receiver (.delivery m))
            (again.foldl (fun n (receiver, m) => advanceV rule n receiver (.delivery m)) net))

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

/-! ## F1, executed: twelve rounds, three leader rotations -/

def rounds : Nat := 12
def prRun : Net := play .pr rounds
def mainRun : Net := play .main rounds
def lateVoteRun : Net := play .prLateVote rounds
/-- Three rounds under the kernel's `step`: short enough for the kernel to replay through
the real `runChecked` (`GenericSimplexJumpReach.reachRun_runChecked`). -/
def reachRun : Net := play .main 3

/-- F1. Under the PR's rule the adversary policy is admitted for twelve rounds (three leader
rotations) and its concrete input list replays to the same states; the honest replicas
reach views 13, 12, 13 (no tick was delivered: every view ended prepared); every view has
exactly two honest VOTEs, where three are needed, and at most one honest COMMIT; no honest
replica commits, delivers or fails. Fairness of the finite run: the only honest messages
not yet delivered are for the last two views (the one-round lag on the 1-2 link). -/
theorem pr_jump_starves_commit :
    prRun.ok = true ∧
    ((runV .pr prRun.schedule).ok && (runV .pr prRun.schedule).states == prRun.states) = true ∧
    currents prRun = [13, 12, 13] ∧
    anyDelivered prRun = false ∧ anyCommitted prRun = false ∧ anyFailed prRun = false ∧
    ((List.range rounds).all fun i => (sentBy prRun (i + 1) .vote).length == 2) = true ∧
    ((List.range rounds).all fun i => decide ((sentBy prRun (i + 1) .commit).length ≤ 1)) = true ∧
    ((undeliveredViews prRun).all fun view => decide (view ≥ rounds - 1)) = true := by
  native_decide

/-- Control. Main's `step` (`stepV_main`) under the same policy commits views 1..10 at all
three honest replicas. The PR run's literal input list is not admitted under main (it
delivers messages only the jumping replicas sent), so the comparison is by policy. -/
theorem main_commits_same_policy :
    mainRun.ok = true ∧ anyFailed mainRun = false ∧
    ((honestStates mainRun).all fun s => s.delivered.length == 10) = true ∧
    ((List.range 10).all fun i =>
      (honestStates mainRun).all fun s => (viewAt s (i + 1)).committed.isSome) = true ∧
    (runV .main prRun.schedule).ok = false := by
  native_decide

/-- Repair. The jump that first casts the late vote in its target view commits views 2..10
under the same policy. This is one schedule, not a progress theorem. -/
theorem late_vote_jump_commits_same_policy :
    lateVoteRun.ok = true ∧ anyFailed lateVoteRun = false ∧
    ((honestStates lateVoteRun).all fun s => s.delivered.length == 9) = true ∧
    ((List.range 9).all fun i =>
      (honestStates lateVoteRun).all fun s => (viewAt s (i + 2)).committed.isSome) = true := by
  native_decide

/-! ## F2, executed: forgetting old views, with and without the commit floor

Rule `.main` throughout (the kernel's `step`). View 1: party 0 proposes `[[1]]`, all three
vote, the votes are delayed. All three time out, send CANDIDATE(⊥), and view 1 is disabled.
View 2: party 1 proposes `[[2]]`, which commits at all three, so each floor is 2. Then the
delayed view-1 votes arrive, with one Byzantine vote and one Byzantine COMMIT.

* `forgetViews` (the kernel's `forget`: views below the floor dropped, the floor kept; the
  audit is kept here because this harness reads it as the record of what was really sent)
  changes nothing: `ingest` refuses the late votes.
* `forgetFloor` drops the views at or below the floor and resets the floor to 0, which is a
  restart that lost its floor: each forgetful replica has lost its CANDIDATE(⊥), sends
  COMMIT for `[[1]]`, and halts. -/

def forgetViews (s : State) : State := { forget s with audit := s.audit }

def forgetFloor (s : State) : State :=
  { s with views := s.views.filter (fun v => decide (v.number > s.lastCommitted)), lastCommitted := 0 }

def noHold (_ _ : Nat) (_ : Message) : Bool := false

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
  let net := settle .main noHold 64 net
  -- One Byzantine COMMIT, so that two forgetful replicas are enough.
  let net := [0, 1, 2].foldl
    (fun n party => advanceV .main n party (.delivery ⟨3, 1, .commit, some [[1]]⟩)) net
  settle .main noHold 64 net

def altered (change : State → State) (parties : List Nat) (net : Net) : Net :=
  { net with states := parties.foldl (fun states p => states.set! p (change states[p]!)) net.states }

def keptMemory : Net := lateVotes rebaseSetup
def droppedWithFloor : Net := lateVotes (altered forgetViews [0, 1, 2] rebaseSetup)
def droppedNoFloorAll : Net := lateVotes (altered forgetFloor [0, 1, 2] rebaseSetup)
def droppedNoFloorTwo : Net := lateVotes (altered forgetFloor [0, 1] rebaseSetup)

/-- F2. Before the late votes: view 1 disabled, `[[2]]` committed in view 2 at all three,
floor 2, all healthy. Then, with the floor kept, forgetting the views at or below it is
harmless (no view-1 COMMIT, nobody fails). With the floor forgotten too every forgetful
replica sends COMMIT for `[[1]]` and ends `failed`: all three; or two (f+1) plus one
Byzantine COMMIT, where the third keeps its floor, refuses the view-1 COMMITs and survives. -/
theorem forgotten_floor_halts :
    (rebaseSetup.ok = true ∧ anyFailed rebaseSetup = false ∧
      ((honestStates rebaseSetup).all fun s =>
        (viewAt s 1).disabled && (viewAt s 2).committed == some [[2]] &&
          s.committedTip == [[2]] && s.lastCommitted == 2) = true) ∧
    (keptMemory.ok = true ∧ anyFailed keptMemory = false ∧ sentBy keptMemory 1 .commit = []) ∧
    (droppedWithFloor.ok = true ∧ anyFailed droppedWithFloor = false ∧
      sentBy droppedWithFloor 1 .commit = []) ∧
    (droppedNoFloorAll.ok = true ∧ sentBy droppedNoFloorAll 1 .commit = [0, 1, 2] ∧
      (honestStates droppedNoFloorAll).all (·.failed) = true) ∧
    (droppedNoFloorTwo.ok = true ∧ sentBy droppedNoFloorTwo 1 .commit = [0, 1] ∧
      (honestStates droppedNoFloorTwo).map (·.failed) = [true, true, false]) := by
  native_decide

/-! ## F3, executed: a replica stranded behind a peer's floor, and commit-evidence transfer

Views 1 and 2 commit normally. View 3 (leader 2): party 0 receives nothing for it before its
timer fires, so it sends CANDIDATE(⊥) and may no longer vote or send COMMIT there. Parties 1
and 2 vote; party 3 votes to both and sends its COMMIT to party 2 only. Party 2 commits view
3 and raises its floor to 3; party 1 has two COMMITs, prepares, and enters view 4. Party 0
needs a third READY for the block, and party 2 takes no view-3 message any more. View 4's
leader is party 3, silent.

The kernel's answer: party 0, stuck past its timeout, repeats its CANDIDATE(⊥); party 2,
whose floor has passed that view, puts its floor evidence (the three COMMITs) in `relay`;
the network forwards it; party 0 commits view 3 and jumps. No input here is out of band:
every delivery is a message some party's `outbox`, `audit` or `relay` holds, plus ticks.
`relayOff` is the control: the same schedule on a network that never forwards `relay`. -/

def tickAll (net : Net) (now : Nat) : Net :=
  settle .main noHold 64 ([0, 1, 2].foldl (fun n party => advanceV .main n party (.tick now)) net)

def strandSetup (relayOff : Bool) : Net :=
  let net := (checks 3).foldl (fun n (receiver, input) => advanceV .main n receiver input)
    { initial .main with relayOff := relayOff }
  let net := settle .main (fun _ receiver m => receiver == 0 && decide (m.view ≥ 3)) 64 net
  let net := advanceV .main net 0 (.tick 100)
  let net := [byz 1 3 .vote, byz 2 3 .vote, byz 2 3 .commit].foldl
    (fun n (receiver, input) => advanceV .main n receiver input) net
  tickAll (settle .main noHold 64 net) 200

/-- Evidence never forwarded: two more rounds of timeouts, every honest message delivered. -/
def stranded : Net := tickAll (tickAll (strandSetup true) 300) 400

/-- Evidence forwarded: the same two rounds of timeouts. -/
def rescued : Net := tickAll (tickAll (strandSetup false) 300) 400

def floors (net : Net) : List Nat := (honestStates net).map (·.lastCommitted)
def tips (net : Net) : List Nat := (honestStates net).map (·.committedTip.length)

/-- F3. On a network that never forwards floor evidence party 0 stays in view 3 at floor 2
and parties 1 and 2 in view 4, which can end neither way, through two further rounds of
timeouts with every honest message delivered. With the evidence forwarded all three reach
floor 3, view 4 times out, and views 5 and 6 commit. -/
theorem stranding_ends_with_floor_evidence :
    (stranded.ok = true ∧ anyFailed stranded = false ∧ currents stranded = [3, 4, 4] ∧
      floors stranded = [2, 2, 3] ∧ tips stranded = [2, 2, 3] ∧ undelivered stranded = []) ∧
    (rescued.ok = true ∧ anyFailed rescued = false ∧ floors rescued = [6, 6, 6] ∧
      tips rescued = [5, 5, 5]) := by
  native_decide

end Minidregg.Verify.GenericSimplexJumpStarvation
