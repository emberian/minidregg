import Kernel.GenericSimplexRelative
import Verify.GenericSimplexWindow

/-! Executed controls for the running replica (`GenericSimplexRelative.Replica`): relative
blocks, the delivery policy, recovery. n = 4, f = 1, timeout 100. Each node's whole
committed chain is kept beside it by the harness (`chains`), as a driver's durable record
would; no replica holds it.

* Same run, both engines: eight operations through the running replicas and through the
  specification's `liveStep` network of `Verify.GenericSimplexWindow` end in the same views,
  floors and committed chains, and no block a replica keeps is longer than two payloads.
* A replica four commits behind asks from its height and is served the four commits in
  order; one twelve commits behind (more than the peers keep) stays behind until the
  commits' own COMMIT messages are replayed to it in order, as a durable record would.
* One member's 4,000 COMMITs for far views leave one held message and no view record; three
  members' COMMITs for one far view and block commit it.
* One member's fifty different VOTEs in one view leave `Config.cap` of them (the
  specification's `ingest` refuses the rest).
* Control: with the origin never moved the same run commits the same chains and keeps
  blocks as long as the history.

Imports the kernel only. -/
namespace Minidregg.Verify.GenericSimplexRelative
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexRelative
set_option autoImplicit false

def cfg : Config := ⟨4, 1, 100, 64, 0⟩

structure Net where
  nodes : Array Replica
  /-- Everything each node has committed, in order. -/
  chains : Array Block := #[[], [], [], []]
  queue : List (Nat × WireMessage) := []
  /-- Receivers cut off: what is sent to them is lost. -/
  cut : List Nat := []
  /-- Every COMMIT sent, in order: what the durable records hold. -/
  commits : List WireMessage := []
  /-- The mutant: never move the origin. -/
  fixedOrigin : Bool := false
  sent : Nat := 0

def stepOf (n : Net) (r : Replica) (input : WireInput) : Replica :=
  if n.fixedOrigin then
    -- `Replica.step` with `rebase` left out: heights stay 0 and the engine keeps whole chains.
    let core := match input with
      | .delivery w => (decode r w).elim r.core fun m => liveStep cfg r.core (.delivery m)
      | .deliveryAt now w => (decode r w).elim r.core fun m => liveStep cfg r.core (.deliveryAt now m)
      | .tick now => liveStep cfg r.core (.tick now)
      | .checked _ records => liveStep cfg r.core (.checked records)
      | .offer payload => liveStep cfg r.core (.offer payload)
      | .poll => liveStep cfg r.core .poll
    { r with core := { core with outbox := [], relay := [], delivered := [] }
             sends := core.outbox.map (encode 0)
             committed := (core.delivered.getLast?.getD []).drop r.core.committedTip.length }
  else r.step cfg input

def act (n : Net) (i : Nat) (input : WireInput) : Net :=
  let (out, next) := (stepOf n n.nodes[i]! input).drain
  let all := (out.sends.flatMap fun m => ((List.range 4).filter (· != i)).map fun r => (r, m)) ++ out.owed
  { n with nodes := n.nodes.set! i next, chains := n.chains.set! i (n.chains[i]! ++ out.committed),
           queue := n.queue ++ all.filter (fun (r, _) => !n.cut.contains r),
           commits := n.commits ++ out.sends.filter (·.kind == .commit),
           sent := n.sent + all.length }

def drain : Nat → Net → Net
  | 0, n => n
  | fuel + 1, n =>
    match n.queue with
    | [] => n
    | batch => drain fuel (batch.foldl (fun n (i, m) => act n i (.delivery m)) { n with queue := [] })

def initial : Net :=
  let nodes := (List.range 4).map fun i => (Replica.start cfg i 0).drain
  drain 64 { nodes := (nodes.map (·.2)).toArray,
             queue := nodes.flatMap fun (out, r) =>
               out.sends.flatMap fun m => ((List.range 4).filter (· != r.core.self)).map fun p => (p, m) }

def tickAll (who : List Nat) (n : Net) (now : Nat) : Net :=
  drain 64 (who.foldl (fun n i => act n i (.tick now)) n)

def payload (k : Nat) : Bytes := [UInt8.ofNat (k / 256), UInt8.ofNat (k % 256)]
def history (k : Nat) : Block := (List.range k).map fun i => payload (i + 1)

/-- The checker of each listed node has replayed the first `k` records: it reports the ones
above what that node has committed. -/
def checkedAll (who : List Nat) (n : Net) (k : Nat) : Net :=
  drain 64 (who.foldl (fun n i =>
    let base := (n.nodes[i]!).records
    act n i (.checked base ((history k).drop base))) n)

def ops (who : List Nat) (n : Net) (first count : Nat) : Net :=
  (List.range count).foldl (fun n i => checkedAll who n (first + i)) n

def heights (n : Net) : List Nat := n.nodes.toList.map (·.height)
def currents (n : Net) : List Nat := n.nodes.toList.map (·.core.current)
def floors (n : Net) : List Nat := n.nodes.toList.map (·.core.lastCommitted)
def kept (n : Net) : List Nat := n.nodes.toList.map (·.core.views.length)

/-- The longest block any replica keeps, anywhere in its state. -/
def longest (n : Net) : Nat :=
  (n.nodes.toList.flatMap fun r =>
    r.core.checked.map List.length ++ [r.core.committedTip.length] ++
    r.core.views.flatMap fun v =>
      (v.received.filterMap fun m => m.value.map List.length) ++ v.prepared.map List.length ++
        v.proposal.toList.map List.length).foldl max 0

/-! ## The same run through both engines -/

def all : List Nat := [0, 1, 2, 3]
def eight : Net := ops all initial 1 8

/-- The specification's network (`liveStep` on whole chains), same operations. -/
def eightSpec : GenericSimplexWindow.Net :=
  (List.range 8).foldl (fun n i => GenericSimplexWindow.checkedAll n (history (i + 1)))
    GenericSimplexWindow.initial

theorem same_run_both_engines :
    eight.chains.toList = eightSpec.nodes.toList.map (·.committedTip) ∧
    eight.chains.toList = [history 8, history 8, history 8, history 8] ∧
    currents eight = GenericSimplexWindow.currents eightSpec ∧
    floors eight = GenericSimplexWindow.floors eightSpec ∧
    heights eight = [8, 8, 8, 8] ∧ (longest eight ≤ 2) ∧
    (eight.nodes.all fun r => !r.core.failed && r.core.committedTip.isEmpty) = true := by
  native_decide

/-! ## Recovery -/

/-- Node 0 is cut off while the other three commit `missed` operations (each followed by
three rounds of their timeouts, which end the views node 0 leads). Then it is reconnected,
one more operation is checked everywhere, and everyone runs `rounds` rounds of timeouts. -/
def lagged (missed rounds : Nat) : Net :=
  let n := ops all initial 1 1
  let n := (List.range missed).foldl (fun n i =>
    (List.range 3).foldl (fun n k => tickAll [1, 2, 3] n ((i + 1) * 1000 + k * 100))
      (checkedAll [1, 2, 3] n (2 + i))) { n with cut := [0] }
  let n := checkedAll all { n with cut := [] } (2 + missed)
  (List.range rounds).foldl (fun n t => tickAll all n ((missed + 2) * 1000 + t * 100)) n

/-- The durable transfer: every COMMIT ever sent, replayed to node 0 in the order sent. -/
def replayed (n : Net) : Net :=
  drain 64 (n.commits.foldl (fun n m => if m.sender == 0 then n else act n 0 (.delivery m)) n)

def shallow : Net := lagged 4 6
def deep : Net := lagged 12 6
def deepReplayed : Net :=
  (List.range 6).foldl (fun n t => tickAll all n (20000 + t * 100)) (replayed deep)

theorem recovery :
    -- Four commits behind (the peers keep eight): served on asking, everything commits.
    (heights shallow = [6, 6, 6, 6] ∧ shallow.chains.toList = [history 6, history 6, history 6, history 6]) ∧
    -- Twelve behind: no peer keeps the commit after node 0's height. It stays where it was.
    (heights deep = [1, 14, 14, 14] ∧ (deep.nodes[0]!).far.length ≤ 4 ∧ (kept deep).all (· ≤ 12) = true) ∧
    -- The durable record replayed in order: node 0 commits the same chain.
    (heights deepReplayed = [14, 14, 14, 14] ∧ deepReplayed.chains[0]! = history 14) := by
  native_decide

/-! ## The delivery policy -/

def one : Net := ops all initial 1 1

def farCommit (sender view : Nat) (block : Block) : WireMessage := ⟨sender, view, .commit, 1, some block⟩

/-- Member 3 names 4,000 far views to node 0. -/
def spam : Net :=
  (List.range 4000).foldl (fun n i => act n 0 (.delivery (farCommit 3 (1000 + i) [payload 2]))) one

/-- Node 0's checker has replayed record 2; members 1, 2, 3 send COMMIT for it in view 40. -/
def farQuorum (senders : List Nat) : Net :=
  let n := act one 0 (.checked 1 [payload 2])
  drain 64 (senders.foldl (fun n s => act n 0 (.delivery (farCommit s 40 [payload 2]))) n)

/-- Member 3 votes for fifty different blocks in view 2. -/
def equivocation : Net :=
  (List.range 50).foldl (fun n i =>
    act n 0 (.delivery ⟨3, 2, .vote, 1, some [payload (100 + i)]⟩)) one

theorem delivery_policy :
    (kept spam = kept one ∧ (spam.nodes[0]!).far.length = 1 ∧ heights spam = heights one) ∧
    ((farQuorum [1, 2]).chains[0]! = history 1 ∧ ((farQuorum [1, 2]).nodes[0]!).far.length = 2 ∧
      (kept (farQuorum [1, 2]))[0]! = (kept one)[0]!) ∧
    ((farQuorum [1, 2, 3]).chains[0]! = history 2 ∧ ((farQuorum [1, 2, 3]).nodes[0]!).core.lastCommitted = 40 ∧
      ((farQuorum [1, 2, 3]).nodes[0]!).core.current = 41 ∧ ((farQuorum [1, 2, 3]).nodes[0]!).far = []) ∧
    (((viewAt (equivocation.nodes[0]!).core 2).received.filter fun m => m.sender == 3).length = cfg.cap) := by
  native_decide

/-! ## Equivocation survives a commit

Node 0 is in view 2 at height 1. Member 3 sends it two VOTEs for view 3: one for a block
that will not extend the next commit, one for a block that will. Record 2 then commits in
view 2 and the origin moves. The first vote's block is gone; member 3 is still excluded
from view 3's VOTE counts, as in the specification, where nothing is forgotten. -/

def twoVotes : Net :=
  [[[9, 9]], [payload 2, [9, 8]]].foldl (fun n block =>
    act n 0 (.delivery ⟨3, 3, .vote, 1, some block⟩)) one

def twoVotesCommitted : Net := checkedAll all twoVotes 2

theorem equivocation_survives_commit :
    voteEquivocator (viewAt (twoVotes.nodes[0]!).core 3) 3 = true ∧
    heights twoVotesCommitted = [2, 2, 2, 2] ∧
    ((viewAt (twoVotesCommitted.nodes[0]!).core 3).received.map (·.value)) = [some [], some [[9, 8]]] ∧
    voteEquivocator (viewAt (twoVotesCommitted.nodes[0]!).core 3) 3 = true ∧
    count (viewAt (twoVotesCommitted.nodes[0]!).core 3) .vote (some [[9, 8]]) = 0 := by
  native_decide

/-! ## Control: the origin never moved -/

def eightFixed : Net := ops all { initial with fixedOrigin := true } 1 8

/-- With the origin fixed at 0 the wire says height 0 and whole chains: the same chains
commit, and the replicas keep blocks as long as the history. Moving the origin is what
bounds them. -/
theorem fixed_origin_grows :
    eightFixed.chains.toList = [history 8, history 8, history 8, history 8] ∧ longest eightFixed = 8 := by
  native_decide

end Minidregg.Verify.GenericSimplexRelative
