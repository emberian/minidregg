import Kernel.GenericSimplexSupportExtends
import Theory.AssertCompiled
import Verify.GenericSimplexRelative

/-! Agreement for the running replicas (`GenericSimplexRelative.Replica`), as a transport of
the specification's.

* `RelNetwork`, `RelReachable`: the network of running replicas, with each one's durable
  record (the chain it has committed, every message it has sent and the chain it was sent
  from). Authentication (`RelAuthentic`) is the specification's, on wire messages.
* `RelativeFaithful` (STATEMENT, no proof): every reachable network of running replicas has
  a trace of the abstract model (`LocalFaithful`) that is its own: its correct members'
  sends are exactly the durable record and each correct replica's chain is a commit of it.
* `relative_agreement_of_faithful` (proved): with that, the abstract model's agreement
  theorem (`committed_prefix_consistency`) is the running replicas' (`RelativeAgreement`).
* Witnesses: `relNet_reachable` (premise inhabitation: a reachable `RelNetwork` whose
  correct replicas have committed), `relNet_faithful` (the conclusion holds there, with the
  trace of the specification's run of the same operation), `conflict_not_agreement` (teeth: the conclusion refuses a network of two conflicting
  chains). -/
namespace Minidregg.Verify.GenericSimplexRelativeReach
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexRelative
open Minidregg.Verify.GenericSimplexRelative (plain plain_collisionFree)
open Minidregg.Kernel.GeneralSimplexReachability
open Minidregg.Kernel.GenericSimplexObservationSafety
open Minidregg.Kernel.GenericSimplexVAInvariant
open Minidregg.Kernel.GenericSimplexEngineSafety
set_option autoImplicit false

structure RelNetwork where
  replica : Nat → Replica
  /-- Everything the replica has committed, in order. -/
  chain : Nat → Block
  /-- Every message the replica has sent, with its committed chain after the step that sent it. -/
  sent : Nat → List (Block × WireMessage)

/-- The whole-chain message a wire message denotes at a replica that has committed `chain`. -/
def denote (chain : Block) (w : WireMessage) : Message :=
  ⟨w.sender, w.view, w.kind, w.value.map fun run => chain.take w.height ++ run⟩

/-- A message of a correct member is one that member sent, as it sent it. A COMMIT is
authentic as what was signed, the view and the statement: its height and block are written
by whoever passes it on, and the receiver checks them against the statement (`decode`,
`commit_reads_signed_chain`). -/
def RelAuthentic (c : Config) (faulty : Finset Nat) (net : RelNetwork) (w : WireMessage) : Prop :=
  w.sender < c.parties ∧ (w.sender ∈ faulty ∨ ∃ entry ∈ net.sent w.sender,
    if w.kind = .commit then
      entry.2.sender = w.sender ∧ entry.2.kind = .commit ∧ entry.2.view = w.view ∧
        entry.2.statement = w.statement
    else entry.2 = w)

/-- `checked party history`: the party's checker has replayed that source history. -/
def RelAllowed (c : Config) (faulty : Finset Nat) (checked : Nat → Block → Prop)
    (net : RelNetwork) (receiver : Nat) (input : WireInput) : Prop :=
  receiver < c.parties ∧ receiver ∉ faulty ∧
  match input with
  | .delivery w | .deliveryAt _ w => RelAuthentic c faulty net w
  | .checked height records => height ≤ (net.replica receiver).records ∧
      checked receiver ((applicationHistory (net.chain receiver)).take height ++ records)
  | .tick _ | .offer _ | .poll => True

def relInitial (c : Config) (h : ChainDigest) (time : Nat) : RelNetwork :=
  { replica := fun party => (Replica.start c h party time).drain.2
    chain := fun _ => []
    sent := fun party => (Replica.start c h party time).drain.1.sends.map fun m => ([], m) }

def relAdvance (c : Config) (h : ChainDigest) (net : RelNetwork) (party : Nat) (input : WireInput) : RelNetwork :=
  let result := ((net.replica party).step c h input).drain
  { replica := fun other => if other = party then result.2 else net.replica other
    chain := fun other => if other = party then net.chain party ++ result.1.committed else net.chain other
    sent := fun other =>
      if other = party then
        -- The chain after the step: a message sent after a commit inside this step is
        -- relative to the new height, and `denote` takes the chain up to the message's own.
        net.sent party ++ (result.1.sends ++ (result.1.owed.map (·.2)).filter (·.sender == party)).map
          fun m => (net.chain party ++ result.1.committed, m)
      else net.sent other }

inductive RelReachable (c : Config) (h : ChainDigest) (faulty : Finset Nat) (checked : Nat → Block → Prop)
    (time : Nat) : RelNetwork → Prop where
  | initial : RelReachable c h faulty checked time (relInitial c h time)
  | next {net : RelNetwork} (prior : RelReachable c h faulty checked time net)
      (party : Nat) (input : WireInput) (allowed : RelAllowed c faulty checked net party input) :
      RelReachable c h faulty checked time (relAdvance c h net party input)

/-- The conclusion: two correct replicas' committed chains are prefix-comparable. -/
def Agrees (c : Config) (faulty : Finset Nat) (net : RelNetwork) : Prop :=
  ∀ p q, p < c.parties → q < c.parties → p ∉ faulty → q ∉ faulty →
    net.chain p <+: net.chain q ∨ net.chain q <+: net.chain p

/-- Agreement of the running replicas, for a digest with no collisions. -/
def RelativeAgreement : Prop :=
  ∀ {c : Config} {h : ChainDigest} {faulty : Finset Nat} {checked : Nat → Block → Prop} {time : Nat}
    {net : RelNetwork}, h.CollisionFree → RelReachable c h faulty checked time net →
    c.parties = 3 * c.faults + 1 → faulty.card ≤ c.faults → Agrees c faulty net

/-- What it is for a trace of the abstract model to be this network's. `rules`: the trace
meets every local obligation of the model the specification's safety theorem is proved on.
`commits`: each correct replica's chain is a commit of that trace. `sends`, `only`: on the
messages of correct members the trace is exactly the durable record, read as whole chains
(`denote`), so the trace cannot give a correct member a message it did not send, or omit
one it did. -/
structure Faithful (c : Config) (faulty : Finset Nat) (net : RelNetwork) (tr : Trace) : Prop where
  rules : LocalFaithful tr (Finset.range c.parties) faulty c.faults
  commits : ∀ p, p < c.parties → p ∉ faulty → ∃ view, CommittedAt tr faulty view (net.chain p)
  sends : ∀ p, p < c.parties → p ∉ faulty → ∀ entry ∈ net.sent p, entry.2.sender = p →
    ∃ t, tr t = .send (denote entry.1 entry.2)
  only : ∀ t m, tr t = .send m → m.sender < c.parties → m.sender ∉ faulty →
    ∃ entry ∈ net.sent m.sender, denote entry.1 entry.2 = m

/-- STATEMENT (no proof). Every reachable network of running replicas has a trace of the
abstract model that is its own (`Faithful`). This replaces `RelativeRefines`, which asked
for a reachable network of the specification's `step` with the same views and floors: the
running replica is knowingly not an image of `step` (it notes a member ahead when it cannot
read its block, it has room under the cap again after a commit drops a member's
conflicting messages, and it takes an offer of a payload it has already committed), and
none of that is read by the abstract model, where the safety theorem lives.

The proof owed is an induction on the run. Its two external facts are proved:
`GenericSimplexSupportExtends.support_extends_commit` (what a correct member supports above
a committed view strictly extends the commit, so `decode` reads the chain the sender meant
by `above_denotes` and `rebase` drops nothing a correct member sent by `strip_conflict`) and
`conflicting_count_small` (a tombstone's value is counted for at most `faults` members).
What remains is the local half: each event of one `liveStep` on relative blocks, read
through `denote`, meets its `LocalFaithful` obligation from the messages the replica holds.

The digest must have no collisions (`ChainDigest.CollisionFree`, inhabited by
`GenericSimplexRelative.plain_collisionFree`): a COMMIT is authentic as its statement, and
the block a replica reads under it is the signed chain only then (`commit_reads_signed_chain`).

satisfiable / premise-inhabitation: `relNet_faithful` (a reachable network whose correct
replicas have committed, with its trace). teeth: `conflict_not_agreement` through
`relative_agreement_of_faithful`. -/
def RelativeFaithful : Prop :=
  ∀ {c : Config} {h : ChainDigest} {faulty : Finset Nat} {checked : Nat → Block → Prop} {time : Nat}
    {net : RelNetwork}, h.CollisionFree → RelReachable c h faulty checked time net →
    c.parties = 3 * c.faults + 1 → faulty.card ≤ c.faults → ∃ tr, Faithful c faulty net tr

/-- The abstract model's agreement theorem is the running replicas'. -/
theorem relative_agreement_of_faithful (faithful : RelativeFaithful) : RelativeAgreement := by
  intro c h faulty checked time net free reachable size faultBound p q pm qm ph qh
  obtain ⟨tr, own⟩ := faithful free reachable size faultBound
  obtain ⟨v, left⟩ := own.commits p pm ph
  obtain ⟨w, right⟩ := own.commits q qm qh
  exact committed_prefix_consistency own.rules (by simpa using size) faultBound left right

/-! ## Witnesses -/

/-- Admission, executable, for the pole committee (party 3 faulty, every history checked). -/
def relAllowedB (net : RelNetwork) (receiver : Nat) (input : WireInput) : Bool :=
  decide (receiver < poleConfig.parties) && receiver != 3 &&
  match input with
  | .delivery w | .deliveryAt _ w =>
      decide (w.sender < poleConfig.parties) &&
        (w.sender == 3 || (net.sent w.sender).any fun entry =>
          if w.kind = .commit then
            decide (entry.2.sender = w.sender ∧ entry.2.kind = .commit ∧ entry.2.view = w.view ∧
              entry.2.statement = w.statement)
          else decide (entry.2 = w))
  | .checked height _ => decide (height ≤ (net.replica receiver).records)
  | .tick _ | .offer _ | .poll => true

theorem relAllowedB_sound {net : RelNetwork} {receiver : Nat} {input : WireInput}
    (ok : relAllowedB net receiver input = true) :
    RelAllowed poleConfig poleFaulty (fun _ _ => True) net receiver input := by
  unfold relAllowedB at ok
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at ok
  obtain ⟨⟨member, honest⟩, rest⟩ := ok
  refine ⟨member, by simpa [poleFaulty] using honest, ?_⟩
  cases input with
  | delivery w | deliveryAt _ w =>
    rw [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at rest
    refine ⟨rest.1, ?_⟩
    rcases rest.2 with byzantine | sent
    · left; simpa [poleFaulty] using byzantine
    · right
      obtain ⟨entry, member, same⟩ := List.any_eq_true.mp sent
      refine ⟨entry, member, ?_⟩
      split at same <;> rename_i commit
      · simp only [commit, ↓reduceIte]; exact of_decide_eq_true same
      · simp only [commit, ↓reduceIte]; exact of_decide_eq_true same
  | checked height records => exact ⟨of_decide_eq_true rest, trivial⟩
  | tick _ | offer _ | poll => trivial

def relRun : RelNetwork → List (Nat × WireInput) → Option RelNetwork
  | net, [] => some net
  | net, (party, input) :: rest =>
      if relAllowedB net party input then relRun (relAdvance poleConfig plain net party input) rest else none

theorem relRun_reachable {time : Nat} (net result : RelNetwork) (inputs : List (Nat × WireInput))
    (reachable : RelReachable poleConfig plain poleFaulty (fun _ _ => True) time net)
    (run : relRun net inputs = some result) :
    RelReachable poleConfig plain poleFaulty (fun _ _ => True) time result := by
  induction inputs generalizing net with
  | nil => cases run; exact reachable
  | cons head rest ih =>
    obtain ⟨party, input⟩ := head
    unfold relRun at run
    split at run
    · rename_i ok
      exact ih _ (.next reachable party input (relAllowedB_sound ok)) run
    · cases run

/-- One operation: the three correct replicas' checkers report record `[7]`, then every
message a correct replica has sent is delivered to the other two, round after round. -/
def poleSchedule : Nat → RelNetwork → List (Nat × WireInput) → List (Nat × WireInput) × RelNetwork
  | 0, net, done => (done, net)
  | fuel + 1, net, done =>
      let pending := [0, 1, 2].flatMap fun receiver => [0, 1, 2].flatMap fun sender =>
        if sender == receiver then [] else (net.sent sender).filterMap fun entry =>
          if done.contains (receiver, .delivery entry.2) then none
          else some (receiver, WireInput.delivery entry.2)
      if pending.isEmpty then (done, net) else
      poleSchedule fuel (pending.foldl (fun net step => relAdvance poleConfig plain net step.1 step.2) net)
        (done ++ pending)

def poleInputs : List (Nat × WireInput) :=
  let checks : List (Nat × WireInput) := [0, 1, 2].map fun party => (party, .checked 0 [[7]])
  (poleSchedule 16
    (checks.foldl (fun net step => relAdvance poleConfig plain net step.1 step.2) (relInitial poleConfig plain 0))
    checks).1

/-- Premise inhabitation: the schedule is admitted from the real start, and the three
correct replicas have each committed `[[7]]` and moved their origin to height 1. -/
theorem relNet_run :
    ((relRun (relInitial poleConfig plain 0) poleInputs).map fun net =>
      [0, 1, 2].map fun party => (net.chain party, (net.replica party).height,
        (net.replica party).core.committedTip)) =
      some [([[7]], 1, []), ([[7]], 1, []), ([[7]], 1, [])] := by
  native_decide

/-! The specification's run of the same operation, for the trace. -/

/-- Every message a correct replica has sent is delivered to the other two, round after round. -/
def specFlood : Nat → Network → List (Nat × Input) → List (Nat × Input) × Network
  | 0, net, done => (done, net)
  | fuel + 1, net, done =>
      let pending := [0, 1, 2].flatMap fun receiver => [0, 1, 2].flatMap fun sender =>
        if sender == receiver then [] else (net.localState sender).audit.filterMap fun event =>
          match event with
          | .send m => if done.contains (receiver, .delivery m) then none else some (receiver, Input.delivery m)
          | _ => none
      if pending.isEmpty then (done, net) else
      specFlood fuel (pending.foldl (fun net step => advance poleConfig poleFaulty net step.1 step.2) net)
        (done ++ pending)

def specInputs : List (Nat × Input) :=
  let checks : List (Nat × Input) := [0, 1, 2].map fun party => (party, .checked [[7]])
  (specFlood 16
    (checks.foldl (fun net step => advance poleConfig poleFaulty net step.1 step.2) (initial poleConfig 0))
    checks).1

def specNet : Network :=
  (runChecked poleConfig poleFaulty (initial poleConfig 0) specInputs).getD (initial poleConfig 0)

def relNet : RelNetwork := (relRun (relInitial poleConfig plain 0) poleInputs).getD (relInitial poleConfig plain 0)

/-- Executed: the specification admits its schedule and commits `[[7]]` in view 1; the
running replicas' durable record of their own sends, read as whole chains, is exactly the
correct members' sends of the specification's run. -/
theorem relNet_trace :
    (runChecked poleConfig poleFaulty (initial poleConfig 0) specInputs).isSome = true ∧
    specNet.audit.contains (.commit 0 1 [[7]]) = true ∧
    ([0, 1, 2].all fun p => (relNet.sent p).all fun entry =>
      entry.2.sender != p || specNet.audit.contains (.send (denote entry.1 entry.2))) = true ∧
    (specNet.audit.all fun event =>
      match event with
      | .send m => decide (4 ≤ m.sender) || m.sender == 3 ||
          (relNet.sent m.sender).any fun entry => denote entry.1 entry.2 == m
      | _ => true) = true := by
  native_decide

theorem specNet_reachable : Reachable poleConfig poleFaulty poleChecked 0 specNet := by
  unfold specNet
  rcases run : runChecked poleConfig poleFaulty (initial poleConfig 0) specInputs with _ | net
  · have admitted := relNet_trace.1
    rw [run] at admitted
    simp at admitted
  · exact runChecked_reachable specInputs _ net .initial run

theorem relNet_reachable : RelReachable poleConfig plain poleFaulty (fun _ _ => True) 0 relNet ∧
    ∀ party, party < 3 → relNet.chain party = [[7]] := by
  unfold relNet
  rcases run : relRun (relInitial poleConfig plain 0) poleInputs with _ | net
  · have executed := relNet_run
    rw [run] at executed
    simp at executed
  · refine ⟨relRun_reachable _ net _ .initial run, ?_⟩
    have executed := relNet_run
    rw [run] at executed
    simp only [Option.map_some, Option.some.injEq, List.map_cons, List.map_nil, List.cons.injEq,
      Prod.mk.injEq, and_true] at executed
    intro party small
    have cases : party = 0 ∨ party = 1 ∨ party = 2 := by omega
    rcases cases with rfl | rfl | rfl
    · exact executed.1.1
    · exact executed.2.1.1
    · exact executed.2.2.1

/-- Satisfiable: on a reachable network whose correct replicas have committed, the
conclusion of `RelativeFaithful` holds, with the trace of the specification's run. -/
theorem relNet_faithful : RelReachable poleConfig plain poleFaulty (fun _ _ => True) 0 relNet ∧
    Faithful poleConfig poleFaulty relNet (auditTrace specNet) := by
  obtain ⟨_, committed, sends, only⟩ := relNet_trace
  have correct : ∀ p, p < poleConfig.parties → p ∉ poleFaulty → p = 0 ∨ p = 1 ∨ p = 2 := by
    intro p member honest
    have small : p < 4 := member
    have : p ≠ 3 := by simpa [poleFaulty] using honest
    omega
  refine ⟨relNet_reachable.1, actual_local_faithful specNet_reachable poleConfig_size, ?_, ?_, ?_⟩
  · intro p member honest
    have chain : relNet.chain p = [[7]] := relNet_reachable.2 p (by
      rcases correct p member honest with rfl | rfl | rfl <;> decide)
    obtain ⟨index, atIndex⟩ := List.mem_iff_getElem?.mp (List.contains_iff_mem.mp committed)
    exact ⟨1, Or.inr ⟨index, 0, by decide, by rw [chain]; simp only [auditTrace, atIndex, Option.getD_some]⟩⟩
  · intro p member honest entry stored own
    have inList : p ∈ [0, 1, 2] := by
      rcases correct p member honest with rfl | rfl | rfl <;> decide
    have checked := List.all_eq_true.mp (List.all_eq_true.mp sends p inList) entry stored
    rw [Bool.or_eq_true, bne_iff_ne] at checked
    rcases checked with other | present
    · exact absurd own other
    · obtain ⟨index, atIndex⟩ := List.mem_iff_getElem?.mp (List.contains_iff_mem.mp present)
      exact ⟨index, by simp only [auditTrace, atIndex, Option.getD_some]⟩
  · intro t m atTime member honest
    have stored : (.send m : Minidregg.Kernel.GenericSimplex.AuditEvent) ∈ specNet.audit := by
      unfold auditTrace at atTime
      cases found : specNet.audit[t]? with
      | none => rw [found] at atTime; cases atTime
      | some event =>
        rw [found, Option.getD_some] at atTime
        rw [atTime] at found
        exact List.mem_iff_getElem?.mpr ⟨t, found⟩
    have checked := List.all_eq_true.mp only _ stored
    simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at checked
    rcases checked with (large | third) | present
    · exact absurd member (by have : m.sender < 4 := member; omega)
    · exact absurd honest (by simp [poleFaulty, third])
    · obtain ⟨entry, inside, same⟩ := List.any_eq_true.mp present
      exact ⟨entry, inside, beq_iff_eq.mp same⟩

/-! ## Witnesses for the two facts the proof rests on

A second operation on the specification's run: `[[7]]` is committed in view 1 and
`[[7], [8]]` is voted and committed in view 2. Then one VOTE from the faulty member for a
block that does not extend the commit, in view 3. -/

def twoInputs : List (Nat × Input) :=
  let first := specInputs
  let after := first.foldl (fun net step => advance poleConfig poleFaulty net step.1 step.2) (initial poleConfig 0)
  let checks : List (Nat × Input) := [0, 1, 2].map fun party => (party, .checked [[7], [8]])
  (specFlood 16
    (checks.foldl (fun net step => advance poleConfig poleFaulty net step.1 step.2) after)
    (first ++ checks)).1 ++ [(0, .delivery ⟨3, 3, .vote, some [[9]]⟩)]

def twoNet : Network :=
  (runChecked poleConfig poleFaulty (initial poleConfig 0) twoInputs).getD (initial poleConfig 0)

theorem twoNet_run :
    (runChecked poleConfig poleFaulty (initial poleConfig 0) twoInputs).isSome = true ∧
    (viewAt (twoNet.localState 0) 1).committed = some [[7]] ∧
    (viewAt (twoNet.localState 0) 2).committed = some [[7], [8]] ∧
    twoNet.audit.contains (.send ⟨1, 1, .vote, some [[7]]⟩) = true ∧
    twoNet.audit.contains (.send ⟨1, 2, .commit, some [[7], [8]]⟩) = true ∧
    count (viewAt (twoNet.localState 0) 2) .vote (some [[7], [8]]) = 3 ∧
    count (viewAt (twoNet.localState 0) 3) .vote (some [[9]]) = 1 := by
  native_decide

theorem twoNet_reachable : Reachable poleConfig poleFaulty poleChecked 0 twoNet := by
  unfold twoNet
  rcases run : runChecked poleConfig poleFaulty (initial poleConfig 0) twoInputs with _ | net
  · have admitted := twoNet_run.1
    rw [run] at admitted
    simp at admitted
  · exact runChecked_reachable twoInputs _ net .initial run

open Minidregg.Kernel.GenericSimplexSupportExtends in
/-- Premise inhabitation for `reachable_support_extends`: a correct replica has committed
`[[7]]` in view 1 and a correct member has sent COMMIT for `[[7], [8]]` in view 2. -/
theorem support_extends_inhabited : StrictlyExtends [[7]] [[7], [8]] :=
  reachable_support_extends twoNet_reachable poleConfig_size poleFaulty_bound
    (p := 1) (q := 0) (w := 1) (v := 2) (kind := .commit) (by decide) (by decide)
    twoNet_run.2.1 (by decide) (by decide) (by decide) (List.contains_iff_mem.mp twoNet_run.2.2.2.2.1)

open Minidregg.Kernel.GenericSimplexSupportExtends in
/-- Teeth: the view must be above the commit. In the committed view itself the same run has
a correct member's VOTE for the committed block, which does not strictly extend it. -/
theorem support_extends_needs_above :
    (viewAt (twoNet.localState 0) 1).committed = some [[7]] ∧
    (.send ⟨1, 1, .vote, some [[7]]⟩ : Minidregg.Kernel.GenericSimplex.AuditEvent) ∈ twoNet.audit ∧
    ¬ StrictlyExtends [[7]] [[7]] :=
  ⟨twoNet_run.2.1, List.contains_iff_mem.mp twoNet_run.2.2.2.1, fun extends_ => by
    have := extends_.2; simp at this⟩

open Minidregg.Kernel.GenericSimplexSupportExtends in
/-- Premise inhabitation for `reachable_counted_extends`: three members are counted for
`[[7], [8]]` in view 2, above the commit of `[[7]]`. -/
theorem counted_extends_inhabited : StrictlyExtends [[7]] [[7], [8]] :=
  reachable_counted_extends twoNet_reachable poleConfig_size poleFaulty_bound
    (p := 0) (q := 0) (w := 1) (v := 2) (kind := .vote) (by decide) (by decide) (by decide) (by decide)
    twoNet_run.2.1 (by decide) (by decide) (by rw [twoNet_run.2.2.2.2.2.1]; decide)

open Minidregg.Kernel.GenericSimplexSupportExtends in
/-- `conflicting_count_small` is met with equality: the faulty member's VOTE for `[[9]]` in
view 3 is counted once at replica 0, which has committed `[[7], [8]]` in view 2. The bound
is `faults`, not zero: a conflicting message is kept and counted, below every threshold. -/
theorem conflicting_count_tight :
    ¬ StrictlyExtends [[7], [8]] [[9]] ∧
    count (viewAt (twoNet.localState 0) 3) .vote (some [[9]]) = poleConfig.faults ∧
    count (viewAt (twoNet.localState 0) 3) .vote (some [[9]]) ≤ poleConfig.faults := by
  have conflict : ¬ StrictlyExtends [[7], [8]] [[9]] := fun extends_ => by
    have := extends_.2; simp at this
  exact ⟨conflict, twoNet_run.2.2.2.2.2.2,
    conflicting_count_small twoNet_reachable poleConfig_size poleFaulty_bound
      (p := 0) (q := 0) (w := 2) (v := 3) (kind := .vote) (by decide) (by decide) (by decide) (by decide)
      twoNet_run.2.2.1 (by decide) (by decide) conflict⟩

/-- Teeth: the conclusion is not idle. A network whose replicas 0 and 1 hold `[[1]]` and
`[[2]]` does not agree. -/
theorem conflict_not_agreement :
    ¬ Agrees poleConfig poleFaulty
      { replica := fun party => (Replica.start poleConfig plain party 0).drain.2
        chain := fun party => if party = 0 then [[1]] else [[2]]
        sent := fun _ => [] } := by
  intro agrees
  have conflict := agrees 0 1 (by decide) (by decide) (by decide) (by decide)
  simp at conflict

#assert_axioms relative_agreement_of_faithful relAllowedB_sound relRun_reachable conflict_not_agreement
#assert_axioms above_denotes decode_encode decode_ahead strip_denotes strip_conflict holdFar_unique
#assert_axioms decode_some commit_reads_signed_chain plain_collisionFree
#assert_compiled GenericSimplexRelative.forged_statement_refused
#assert_compiled relNet_run
#assert_compiled relNet_trace
#assert_compiled relNet_faithful
#assert_compiled GenericSimplexRelative.same_run_both_engines
#assert_compiled GenericSimplexRelative.recovery
#assert_compiled GenericSimplexRelative.delivery_policy
#assert_compiled GenericSimplexRelative.fixed_origin_grows
#assert_compiled GenericSimplexRelative.equivocation_survives_commit
#assert_axioms decode_nonempty
#assert_compiled twoNet_run
#assert_compiled support_extends_inhabited
#assert_compiled conflicting_count_tight
#assert_axioms Minidregg.Kernel.GenericSimplexSupportExtends.support_has_honest_vote
#assert_axioms Minidregg.Kernel.GenericSimplexSupportExtends.vote_extends_commit
#assert_axioms Minidregg.Kernel.GenericSimplexSupportExtends.support_extends_commit
#assert_axioms Minidregg.Kernel.GenericSimplexSupportExtends.reachable_support_extends
#assert_axioms Minidregg.Kernel.GenericSimplexSupportExtends.reachable_counted_extends
#assert_axioms Minidregg.Kernel.GenericSimplexSupportExtends.conflicting_count_small

end Minidregg.Verify.GenericSimplexRelativeReach
