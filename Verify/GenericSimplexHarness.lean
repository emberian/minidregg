import Kernel.GenericSimplex
namespace Minidregg.Verify.GenericSimplexHarness
open Minidregg.Kernel.GenericSimplex
set_option autoImplicit false
def cfg : Config := ⟨4,1,70,8⟩
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
def main : IO Unit := do
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
