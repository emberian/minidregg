import Kernel.GenericSimplex
namespace Minidregg.Verify.GenericSimplexHarness
open Minidregg.Kernel.GenericSimplex
set_option autoImplicit false
def cfg : Config := ⟨4,1,70,8,0⟩
def payload : Bytes := [42]
def block : Block := [payload]
structure Network where
  nodes : Array State
  logs : Array (List Input)
  queue : List (Nat × Message)
  deriving Repr
def emissions (old next : State) : List (Nat × Message) :=
  (next.outbox.drop old.outbox.length).flatMap fun m =>
    ((List.range cfg.parties).filter (fun i => i != next.self)).map (fun i => (i,m))
def initial : Network := Id.run do
  let nodes := (List.range cfg.parties).map fun i => start cfg i 0 [payload] [block,[[43]]]
  let queue := nodes.flatMap fun s =>
    s.outbox.flatMap fun m => ((List.range cfg.parties).filter (fun i => i != s.self)).map (fun i => (i,m))
  return ⟨nodes.toArray,Array.replicate cfg.parties [],queue⟩
def act (n : Network) (i : Nat) (input : Input) : Network :=
  let old := n.nodes[i]!
  let next := step cfg old input
  {nodes := n.nodes.set! i next,
   logs := n.logs.set! i (n.logs[i]! ++ [input]),
   queue := n.queue ++ emissions old next}
def dispatch (n : Network) (drop : Message → Bool := fun _ => false) : Network :=
  match n.queue with
  | [] => n
  | (i,m)::rest =>
    let n := {n with queue := rest}
    if drop m then n else act n i (.delivery m)
def run : Nat → Network → (Message → Bool) → Network
  | 0,n,_ => n
  | fuel+1,n,drop =>
    if n.nodes.all (fun s => !s.committedTip.isEmpty) then n
    else if n.queue.isEmpty then n else run fuel (dispatch n drop) drop
def runUntil : Nat → Network → (Network → Bool) → Network
  | 0,n,_ => n
  | fuel+1,n,done =>
    if done n || n.queue.isEmpty then n else runUntil fuel (dispatch n) done

def tickAll (n : Network) (time : Nat) : Network :=
  (List.range cfg.parties).foldl (fun n i => act n i (.tick time)) n
def safe (n : Network) : Bool :=
  n.nodes.all (fun s => !s.failed) &&
  n.nodes.all (fun s => n.nodes.all fun t =>
    isPrefix s.committedTip t.committedTip || isPrefix t.committedTip s.committedTip)
def restarted (n : Network) : Bool :=
  (List.range cfg.parties).all fun i =>
    (n.logs[i]!.foldl (step cfg) (start cfg i 0 [payload] [block,[[43]]])) == n.nodes[i]!
def ensure (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)
def honestSafe (n : Network) : Bool :=
  let honest := n.nodes.toList.take 3
  honest.all (fun s => !s.failed) &&
    honest.all (fun s => honest.all fun t =>
      isPrefix s.committedTip t.committedTip || isPrefix t.committedTip s.committedTip)
def hostileSeed : Network :=
  (List.range 4).foldl (fun n v =>
    [Kind.vote,Kind.commit,Kind.candidate,Kind.ready].foldl (fun n k =>
      [some block,some [[43]],none].foldl (fun n arg =>
        (List.range 3).foldl (fun n i =>
          act n i (.delivery ⟨3,v+1,k,arg⟩)) n) n) n) initial
def adversarial : Nat → Nat → Network → IO Network
  | 0,_,n => pure n
  | fuel+1,seed,n => do
      ensure (honestSafe n) "adversarial honest-prefix conflict"
      let seed := (seed * 1103515245 + 12345) % 2147483648
      if n.queue.isEmpty then return n
      let index := seed % n.queue.length
      let some (i,m) := n.queue[index]? | throw (IO.userError "schedule index")
      let n := {n with queue := n.queue.take index ++ n.queue.drop (index+1)}
      let n := if m.sender == 3 then n else act n i (.delivery m)
      let n := if fuel % 64 == 0 then tickAll n (1000-fuel) else n
      adversarial fuel seed n
/-! ## Timed reproduction of the 00f711 stall (R2-3)

Every emitted message gets an explicit arrival time per recipient and every
replica ticks on a fixed period. The schedule is the recorded one: in views 1
and 2 the VOTEs addressed to replicas 0 and 1 arrive after those replicas'
view deadlines, while replicas 2 and 3 collect q VOTEs inside theirs. So 2 and
3 send COMMIT, 0 and 1 send CANDIDATE(⊥) first, and since a replica that sent
CANDIDATE(⊥) never sends COMMIT for that view, no view gathers q = 3 COMMITs.
Afterwards every message takes 1.5·timeout, ten times the paper's timeout/7
premise: under the fixed timer every replica fires CANDIDATE(⊥) before any
proposal arrives, so no later view commits, while the backoff timer outgrows
the delay. Two operations are offered once, at start, the second extending
the first (a leader proposes only with work, so view 2 needs the second);
nothing resubmits. -/
def payload2 : Bytes := [45]
def block2 : Block := [payload,payload2]
structure Timed where
  cfg : Config
  nodes : Array State
  logs : Array (List Input)
  arrivals : List (Nat × Nat × Message)
  now : Nat

/-- (sendTime, recipient, message) ↦ transit delay. -/
abbrev Delay := Nat → Nat → Message → Nat

def Timed.act (t : Timed) (delay : Delay) (i : Nat) (input : Input) : Timed :=
  let old := t.nodes[i]!
  let next := step t.cfg old input
  let fresh := next.outbox.drop old.outbox.length
  let sent := fresh.flatMap fun m =>
    ((List.range t.cfg.parties).filter (· != i)).map fun r => (t.now + delay t.now r m,r,m)
  let nodes := t.nodes.set! i next
  let logs := t.logs.set! i (t.logs[i]! ++ [input])
  { t with nodes := nodes, logs := logs, arrivals := t.arrivals ++ sent }

def Timed.initial (cfg : Config) (delay : Delay) (offers : List Bytes := [payload,payload2])
    (checked : List Block := [block,block2]) : Timed := Id.run do
  let nodes := (List.range cfg.parties).map fun i => start cfg i 0 offers checked
  let arrivals := nodes.flatMap fun s =>
    s.outbox.flatMap fun m => ((List.range cfg.parties).filter (· != s.self)).map fun r => (delay 0 r m,r,m)
  return ⟨cfg,nodes.toArray,Array.replicate cfg.parties [],arrivals,0⟩

/-- Deliver the earliest due arrival (stable among equal times), else tick all. -/
def Timed.advance (t : Timed) (delay : Delay) (period : Nat) : Timed :=
  let nextTick := (t.now / period + 1) * period
  let earliest := t.arrivals.zipIdx.foldl (fun best (entry,index) =>
    match best with
    | none => if entry.1 ≤ nextTick then some (entry,index) else none
    | some (b,_) => if entry.1 < b.1 then some (entry,index) else best) none
  match earliest with
  | some ((time,recipient,m),index) =>
    let t := {t with now := max t.now time, arrivals := t.arrivals.eraseIdx index}
    t.act delay recipient (.deliveryAt t.now m)
  | none =>
    let t := {t with now := nextTick}
    (List.range t.cfg.parties).foldl (fun t i => t.act delay i (.tick nextTick)) t

def Timed.runUntil (t : Timed) (delay : Delay) (period stop : Nat) : Nat → Timed
  | 0 => t
  | fuel+1 => if t.now ≥ stop then t else (t.advance delay period).runUntil delay period stop fuel

/-- Distinct members that sent COMMIT in this view, across all replicas. -/
def commitSenders (t : Timed) (view : Nat) : List Nat :=
  (t.nodes.toList.flatMap fun s => s.outbox.filter fun m => m.kind == .commit && m.view == view)
    |>.map Message.sender |>.eraseDups

/-- Distinct members that sent CANDIDATE(⊥) (a timeout) in this view. -/
def bottomSenders (t : Timed) (view : Nat) : List Nat :=
  (t.nodes.toList.flatMap fun s => s.outbox.filter fun m => m.kind == .candidate && m.view == view && m.value.isNone)
    |>.map Message.sender |>.eraseDups

def timedSafe (t : Timed) : Bool :=
  let all := t.nodes.toList.flatMap State.delivered
  t.nodes.all (fun s => !s.failed) &&
    all.all fun a => all.all fun b => isPrefix a b || isPrefix b a

def committedPayload (s : State) : Bool := (applicationHistory s.committedTip).contains payload

/-- View in which this replica's tip first carried the payload (0: never). -/
def payloadView (s : State) : Nat :=
  ((s.views.filter fun v => (v.committed.map fun b => (applicationHistory b).contains payload).getD false)
    |>.map View.number |>.foldl (fun acc v => if acc == 0 then v else min acc v) 0)

def noResubmit (t : Timed) : Bool :=
  t.logs.all fun log => log.all fun input =>
    match input with
    | .offer _ | .checked _ => false
    | _ => true

/-- The recorded stall schedule (R2-3 timeline, view 17 onward).
- View 1: the proposal reaches replicas 1, 2, 3 at 0.7·timeout (in the record
  replica 1 validated the new record only late in its window), so every vote
  is cast late. VOTEs to 2 and 3 take 1; VOTEs to 0 and 1 take 1.1·timeout,
  so even the leader's own early VOTE reaches replica 1 after its deadline:
  neither 0 nor 1 holds f+1 VOTEs, hence neither can relay CANDIDATE(b) and
  reach READY, before its timer fires.
- View 2: replicas 0 and 1 enter it about 0.1·timeout after 2 and 3, so the
  leader's (replica 1) proposal reaches 2 and 3 inside their windows. VOTEs to
  0 and 1 take 2.5·timeout, longer than their view-2 timer under both the fixed
  timer (timeout) and the backoff timer (2·timeout, one view since a commit).
- Every other message in views 1 and 2 takes 1; from view 3 on every message
  takes 1.5·timeout (an underestimated Δ: the fixed timer needs Δ ≤ timeout/7). -/
def stallDelay (timeout : Nat) : Delay := fun _ recipient m =>
  if m.view ≤ 2 then
    if m.kind == .vote && recipient < 2 then
      if m.view == 1 then 11 * timeout / 10 else 5 * timeout / 2
    else if m.kind == .propose && m.view == 1 then 7 * timeout / 10
    else 1
  else 15 * timeout / 10

def main : IO Unit := do
  -- (1) The recorded stall, under the paper's fixed timer and under backoff.
  for cap in [0,3] do
    let cfgT : Config := {cfg with timeout := 100, backoffCap := cap}
    let stalled := (Timed.initial cfgT (stallDelay 100)).runUntil (stallDelay 100) 10 1500 200000
    IO.println s!"cap {cap}: COMMIT senders view 1 {commitSenders stalled 1} view 2 {commitSenders stalled 2}; CANDIDATE(⊥) senders view 1 {bottomSenders stalled 1} view 2 {bottomSenders stalled 2}"
    for view in [1,2] do
      ensure (commitSenders stalled view == [2,3] || commitSenders stalled view == [3,2])
        s!"cap {cap}: view {view} did not end with exactly the COMMITs of 2 and 3"
      ensure (stalled.nodes.all fun s => (viewAt s view).committed.isNone)
        s!"cap {cap}: view {view} reached a certificate under the stall"
    ensure (timedSafe stalled) s!"cap {cap}: stall broke prefix consistency"
  IO.println "PASS stall reproduced: views 1 and 2 end with exactly 2 COMMITs (replicas 2,3), no certificate"
  (← IO.getStdout).flush
  -- (2) Every later delay is 1.5·timeout. With backoff the pending block
  -- commits with no resubmission, prefix-consistent everywhere; the paper's
  -- fixed timer under the same schedule commits nothing (the falsifier: this
  -- schedule discriminates fix C, it does not pass without it).
  let cfgC : Config := {cfg with timeout := 100, backoffCap := 3}
  let recovered := (Timed.initial cfgC (stallDelay 100)).runUntil (stallDelay 100) 10 4000 400000
  ensure (recovered.nodes.all committedPayload) "backoff: pending block never committed"
  let views := recovered.nodes.toList.map payloadView
  ensure (views.all (fun v => 2 < v && v ≤ 8)) s!"backoff: payload committed outside views 3..8: {views}"
  ensure (noResubmit recovered) "backoff: payload was resubmitted"
  ensure (timedSafe recovered) "backoff: delivered histories not prefix-consistent"
  let fixed := (Timed.initial {cfgC with backoffCap := 0} (stallDelay 100)).runUntil (stallDelay 100) 10 4000 400000
  ensure (fixed.nodes.all fun s => !committedPayload s && s.committedTip.isEmpty)
    "fixed timer committed under the 1.5·timeout schedule: the recovery check does not discriminate backoff"
  ensure (timedSafe fixed) "fixed timer: delivered histories not prefix-consistent"
  IO.println s!"PASS backoff recovery: payload committed at views {views} on all four, no resubmit, delivered prefix-consistent; the fixed timer under the same schedule committed nothing by t=4000 (views reached {fixed.nodes.toList.map (·.current)})"
  -- (3) Idle quiescence: one operation, then nothing. It commits in view 1;
  -- afterwards no leader has work, so no block is proposed and every later
  -- view ends by CANDIDATE(⊥) on the backoff timer. A late offer is proposed
  -- by the then-current leader without waiting for a view change.
  let quick : Delay := fun _ _ _ => 1
  let cfgI : Config := {cfg with timeout := 100, backoffCap := 3}
  let idle := (Timed.initial cfgI quick [payload] [block]).runUntil quick 10 20000 400000
  let proposals (t : Timed) := (t.nodes.toList.flatMap fun s => s.outbox.filter (·.kind == .propose)).length
  ensure (idle.nodes.all fun s => s.committedTip == block)
    "idle: the single operation did not commit, or a later block was committed"
  ensure (proposals idle == 1) s!"idle: {proposals idle} proposals for one operation"
  ensure (idle.nodes.all fun s => s.current ≥ 5) "idle: views stopped advancing"
  ensure (timedSafe idle) "idle: delivered histories not prefix-consistent"
  let lateOffer := (List.range 4).foldl (fun t i => t.act quick i (.checked block2)) idle
  let late := lateOffer.runUntil quick 10 (idle.now + 50) 100000
  ensure (late.nodes.all fun s => s.committedTip == block2)
    "idle: a late offer was not proposed and committed within the current view"
  ensure (timedSafe late) "late offer: delivered histories not prefix-consistent"
  IO.println s!"PASS idle quiescence: 1 proposal for 1 operation over t=20000 (views reached {idle.nodes.toList.map (·.current)}); a late offer committed within {late.now - idle.now} time units of being checked (views now {late.nodes.toList.map (·.current)})"
  let normal := run 4000 initial (fun _ => false)
  ensure (normal.nodes.all (fun s => !s.committedTip.isEmpty)) "normal progress"
  ensure (safe normal && restarted normal) "normal safety/replay"
  -- A source offer learned after consensus already inserted inert blocks must
  -- still be eligible: inert protocol ancestry is not a new source history.
  let delayedOffer := (List.range cfg.parties).foldl
    (fun n i => act n i (.checked [payload,[44]])) normal
  let delayedComplete := runUntil 8000 delayedOffer
    (fun n => n.nodes.all (fun s => s.committedTip.contains [44]))
  ensure (delayedComplete.nodes.all (fun s => s.committedTip.contains [44]))
    "delayed source offer starved behind inert protocol blocks"
  ensure (safe delayedComplete && restarted delayedComplete)
    "delayed offer safety/replay"
  ensure (!(validBlock delayedComplete.nodes[0]! [[99],[44]]))
    "different nonempty source history inherited validation"
  -- Proposer 0 is silent through view1. Every remaining member receives its
  -- timeout and the three correct parties can disable and advance.
  let silent := run 1000 initial (fun m => m.sender == 0)
  let fallback := run 8000 (tickAll silent 100) (fun m => m.sender == 0)
  ensure ((fallback.nodes.toList.drop 1).all (fun s => !s.committedTip.isEmpty)) "silent leader fallback"
  ensure (safe fallback && restarted fallback) "fallback safety/replay"
  -- Byzantine sender3 equivocates. Detection removes both VOTEs from its count.
  let e1 : Message := ⟨3,1,.vote,some block⟩
  let e2 : Message := ⟨3,1,.vote,some [[43]]⟩
  let equiv := (List.range 3).foldl (fun n i =>
    act (act n i (.delivery e1)) i (.delivery e2)) initial
  ensure ((List.range 3).all fun i => voteEquivocator (viewAt equiv.nodes[i]! 1) 3) "equivocation detection"
  let completed := run 4000 equiv (fun _ => false)
  ensure (safe completed && restarted completed) "equivocation safety/replay"
  -- Late old-view traffic remains processed even after advancement.
  let late := act (tickAll completed 1000) 1 (.delivery ⟨0,1,.ready,some block⟩)
  ensure (safe late && restarted late) "late continuation safety/replay"
  -- Forged sender outside roster cannot contribute to any tally.
  let old := initial.nodes[1]!
  let forged := step cfg old (.delivery ⟨4,1,.commit,some block⟩)
  ensure ((viewAt forged 1).received.all (fun m => m.sender < 4)) "roster guard"
  -- Timeout after voting still requests disable, but cannot retract a COMMIT.
  let timed := step cfg normal.nodes[1]! (.tick 100000)
  ensure (safe {normal with nodes := normal.nodes.set! 1 timed}) "disable after commit"
  for seed in List.range 8 do
    let n ← adversarial 256 (seed+1) hostileSeed
    ensure (honestSafe n && restarted n) "adversarial crash replay"
  IO.println "PASS GenericSimplex event harness: normal, silent-leader fallback, equivocation, old-view continuation, crash replay, roster, timeout"
end Minidregg.Verify.GenericSimplexHarness
def main : IO Unit := Minidregg.Verify.GenericSimplexHarness.main
