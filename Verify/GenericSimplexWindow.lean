import Kernel.GenericSimplex

/-! Executed controls for the idle timer and the view window, on the running engine
(`liveStep`, outbox and relay drained after every input). n = 4, f = 1, timeout 100.

* Idle: after one operation commits, two hundred ticks over 10,000 time units send no
  message and end no view; work that then arrives commits in the view the replicas sat in.
* Spam: 3,000 messages from one member for views far above the horizon create no view
  record, leave one `ahead` entry, and give no reason to leave the view. (A COMMIT is the
  one kind the specification takes there; the running replica holds one per member:
  `Verify.GenericSimplexRelative.delivery_policy`.)
* Lag: replicas 1, 2, 3 leave twelve views without a commit while replica 0 hears nothing;
  it then receives its backlog newest first, so everything above its horizon is dropped. It
  walks to view 10 on what it kept, sees three members ahead, asks to leave, repeats, is
  served the others' own messages (`serveViews`) and reaches view 13.
* Lag, control: with `serveViews` answers not forwarded, replica 0 stays in view 10.

Imports the kernel only. -/
namespace Minidregg.Verify.GenericSimplexWindow
open Minidregg.Kernel.GenericSimplex
set_option autoImplicit false

def cfg : Config := ⟨4, 1, 100, 64, 0⟩

structure Net where
  nodes : Array State
  queue : List (Nat × Message) := []
  /-- Messages for replica 0 held back while `hold` is set, oldest first. -/
  held : List Message := []
  hold : Bool := false
  /-- Control: a network that never forwards `relay`. -/
  relayOff : Bool := false
  sent : Nat := 0

def fan (self : Nat) (sent : List Message) : List (Nat × Message) :=
  sent.flatMap fun m => ((List.range cfg.parties).filter (· != self)).map fun r => (r, m)

def act (n : Net) (i : Nat) (input : Input) : Net :=
  let (sent, next) := drainOutbox (liveStep cfg n.nodes[i]! input)
  let (owed, next) := drainRelay next
  let out := fan i sent ++ (if n.relayOff then [] else owed)
  let (to0, rest) := if n.hold then out.partition (fun (r, _) => r == 0) else ([], out)
  { n with nodes := n.nodes.set! i next, queue := n.queue ++ rest,
           held := n.held ++ to0.map (·.2), sent := n.sent + out.length }

def drain : Nat → Net → Net
  | 0, n => n
  | fuel + 1, n =>
    match n.queue with
    | [] => n
    | batch => drain fuel (batch.foldl (fun n (i, m) => act n i (.delivery m)) { n with queue := [] })

def tickAll (who : List Nat) (n : Net) (now : Nat) : Net :=
  drain 64 (who.foldl (fun n i => act n i (.tick now)) n)

def initial : Net :=
  let nodes := (List.range 4).map fun i => start cfg i 0 [] []
  drain 64 { nodes := (nodes.map fun s => (drainOutbox (forget s)).2).toArray,
             queue := nodes.flatMap fun s => fan s.self s.outbox }

def currents (n : Net) : List Nat := n.nodes.toList.map (·.current)
def floors (n : Net) : List Nat := n.nodes.toList.map (·.lastCommitted)
def kept (n : Net) : List Nat := n.nodes.toList.map (·.views.length)

/-! ## Idle -/

def checkedAll (n : Net) (block : Block) : Net :=
  drain 64 ((List.range 4).foldl (fun n i => act n i (.checked block)) n)

def oneOp : Net := checkedAll initial [[7]]
def idle : Net := (List.range 200).foldl (fun n t => tickAll [0, 1, 2, 3] n (t * 50)) oneOp
def lateOp : Net := checkedAll idle [[7], [8]]

#guard floors oneOp == [1, 1, 1, 1] && currents oneOp == [2, 2, 2, 2]
#guard idle.sent == oneOp.sent && currents idle == [2, 2, 2, 2] && kept idle == [2, 2, 2, 2]
#guard floors lateOp == [2, 2, 2, 2] && lateOp.nodes.all fun s => s.committedTip == [[7], [8]]

/-! ## Spam above the horizon -/

def spam (s : State) : State :=
  (List.range 1000).foldl (fun s v =>
    [Kind.vote, .candidate, .ready].foldl (fun s kind =>
      liveStep cfg s (.delivery ⟨3, 20 + v, kind, some [[UInt8.ofNat v]]⟩)) s) s

def spammed : State := spam initial.nodes[1]!

#guard spammed.views.length == initial.nodes[1]!.views.length
#guard spammed.ahead == [(3, 1019)] && !wantsOut cfg spammed
#guard spammed.outbox.isEmpty && spammed.relay.isEmpty

/-! ## A replica behind the window -/

/-- Replicas 1, 2, 3 are given an unchecked proposal in each of twelve views and time each
out; replica 0's messages are held. -/
def twelve (relayOff : Bool) : Net :=
  (List.range 12).foldl (fun n v =>
    let view := v + 1
    let leader := cfg.leader view
    let n := [1, 2, 3].foldl (fun n r =>
      if r != leader then act n r (.delivery ⟨leader, view, .propose, some [[99]]⟩) else n) n
    (List.range 3).foldl (fun n k => tickAll [1, 2, 3] n (view * 300 + k * 100)) n)
    { initial with hold := true, relayOff := relayOff }

/-- Replica 0 receives its backlog newest first. -/
def backlog (n : Net) : Net :=
  n.held.reverse.foldl (fun n m => drain 64 (act n 0 (.delivery m))) { n with held := [], hold := false }

def behind (relayOff : Bool) : Net := backlog (twelve relayOff)
def caughtUp (relayOff : Bool) : Net :=
  (List.range 4).foldl (fun n k => tickAll [0, 1, 2, 3] n (5000 + k * 100)) (behind relayOff)

#guard currents (twelve false) == [1, 13, 13, 13]
#guard currents (behind false) == [10, 13, 13, 13] && floors (behind false) == [0, 0, 0, 0]
#guard (behind false).nodes[0]!.ahead.length == 3 && wantsOut cfg (behind false).nodes[0]!
#guard currents (caughtUp false) == [13, 13, 13, 13]
#guard currents (caughtUp true) == [10, 13, 13, 13]

end Minidregg.Verify.GenericSimplexWindow
