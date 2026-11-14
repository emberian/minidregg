import Kernel.GenericSimplexObservationSafety
import Theory.AssertCompiled
import Verify.GenericSimplexRelative

/-! Agreement for the running replicas (`GenericSimplexRelative.Replica`), as a transport of
the specification's.

* `RelNetwork`, `RelReachable`: the network of running replicas, with each one's durable
  record (the chain it has committed, every message it has sent and the chain it was sent
  from). Authentication (`RelAuthentic`) is the specification's, on wire messages.
* `RelativeRefines` (STATEMENT, no proof): every reachable network of running replicas has
  a reachable network of the specification in which each correct replica has delivered the
  same chain and stands in the same view at the same floor.
* `relative_agreement_of_refines` (proved): with that, the specification's agreement
  theorem (`actual_delivered_blocks_compatible`) is the running replicas' (`RelativeAgreement`).
* Witnesses: `relNet_reachable` (premise inhabitation: a reachable `RelNetwork` whose
  correct replicas have committed), `relNet_agrees` (the conclusion holds there),
  `conflict_not_agreement` (teeth: the conclusion refuses a network of two conflicting
  chains). -/
namespace Minidregg.Verify.GenericSimplexRelativeReach
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexRelative
open Minidregg.Kernel.GeneralSimplexReachability
open Minidregg.Kernel.GenericSimplexObservationSafety
set_option autoImplicit false

structure RelNetwork where
  replica : Nat → Replica
  /-- Everything the replica has committed, in order. -/
  chain : Nat → Block
  /-- Every message the replica has sent, with its committed chain when it sent it. -/
  sent : Nat → List (Block × WireMessage)

/-- The whole-chain message a wire message denotes at a replica that has committed `chain`. -/
def denote (chain : Block) (w : WireMessage) : Message :=
  ⟨w.sender, w.view, w.kind, w.value.map fun run => chain.take w.height ++ run⟩

/-- A message of a correct member is one that member sent, as it sent it. A COMMIT may also
arrive in another encoding (a peer relays its evidence relative to its own height) if it
denotes at the receiver the chain the member's COMMIT denoted where it was sent: natively
the member's signature is over that chain's digest, and the receiver verifies it. -/
def RelAuthentic (c : Config) (faulty : Finset Nat) (net : RelNetwork) (receiver : Nat)
    (w : WireMessage) : Prop :=
  w.sender < c.parties ∧ (w.sender ∈ faulty ∨ ∃ entry ∈ net.sent w.sender,
    entry.2 = w ∨ (w.kind = .commit ∧ w.height ≤ (net.chain receiver).length ∧
      denote (net.chain receiver) w = denote entry.1 entry.2))

/-- `checked party history`: the party's checker has replayed that source history. -/
def RelAllowed (c : Config) (faulty : Finset Nat) (checked : Nat → Block → Prop)
    (net : RelNetwork) (receiver : Nat) (input : WireInput) : Prop :=
  receiver < c.parties ∧ receiver ∉ faulty ∧
  match input with
  | .delivery w | .deliveryAt _ w => RelAuthentic c faulty net receiver w
  | .checked height records => height ≤ (net.replica receiver).records ∧
      checked receiver ((applicationHistory (net.chain receiver)).take height ++ records)
  | .tick _ | .offer _ | .poll => True

def relInitial (c : Config) (time : Nat) : RelNetwork :=
  { replica := fun party => (Replica.start c party time).drain.2
    chain := fun _ => []
    sent := fun party => (Replica.start c party time).drain.1.sends.map fun m => ([], m) }

def relAdvance (c : Config) (net : RelNetwork) (party : Nat) (input : WireInput) : RelNetwork :=
  let result := ((net.replica party).step c input).drain
  { replica := fun other => if other = party then result.2 else net.replica other
    chain := fun other => if other = party then net.chain party ++ result.1.committed else net.chain other
    sent := fun other =>
      if other = party then
        net.sent party ++ (result.1.sends ++ (result.1.owed.map (·.2)).filter (·.sender == party)).map
          fun m => (net.chain party, m)
      else net.sent other }

inductive RelReachable (c : Config) (faulty : Finset Nat) (checked : Nat → Block → Prop)
    (time : Nat) : RelNetwork → Prop where
  | initial : RelReachable c faulty checked time (relInitial c time)
  | next {net : RelNetwork} (prior : RelReachable c faulty checked time net)
      (party : Nat) (input : WireInput) (allowed : RelAllowed c faulty checked net party input) :
      RelReachable c faulty checked time (relAdvance c net party input)

/-- The conclusion: two correct replicas' committed chains are prefix-comparable. -/
def Agrees (c : Config) (faulty : Finset Nat) (net : RelNetwork) : Prop :=
  ∀ p q, p < c.parties → q < c.parties → p ∉ faulty → q ∉ faulty →
    net.chain p <+: net.chain q ∨ net.chain q <+: net.chain p

def RelativeAgreement : Prop :=
  ∀ {c : Config} {faulty : Finset Nat} {checked : Nat → Block → Prop} {time : Nat} {net : RelNetwork},
    RelReachable c faulty checked time net →
    c.parties = 3 * c.faults + 1 → faulty.card ≤ c.faults → Agrees c faulty net

/-- STATEMENT (no proof). The transport: a reachable network of running replicas is, at its
correct replicas, a reachable network of the specification seen through the codec. Each has
delivered there the chain it has committed here, and stands in the same view at the same
floor. The proof owed is an induction on the run with the specification's safety invariants:
a block a correct member supports in a view above a committed view extends the committed
chain, so `decode` reads the chain the sender meant (`above_denotes`), and what `rebase`
drops was sent by no correct member (`strip_conflict`), and a delivery the policy holds or
drops is a delivery the specification's network makes later or never.

satisfiable / premise-inhabitation: `relNet_reachable`; the conclusion on one run through
both engines: `GenericSimplexRelative.same_run_both_engines`. teeth: `conflict_not_agreement`
(what the conclusion refuses, through `relative_agreement_of_refines`). -/
def RelativeRefines : Prop :=
  ∀ {c : Config} {faulty : Finset Nat} {checked : Nat → Block → Prop} {time : Nat} {net : RelNetwork},
    RelReachable c faulty checked time net →
    c.parties = 3 * c.faults + 1 → faulty.card ≤ c.faults →
    ∃ spec : Network, Reachable c faulty (fun _ party block => checked party block) time spec ∧
      ∀ p, p < c.parties → p ∉ faulty →
        (net.chain p = [] ∨ net.chain p ∈ (spec.localState p).delivered) ∧
        (spec.localState p).current = (net.replica p).core.current ∧
        (spec.localState p).lastCommitted = (net.replica p).core.lastCommitted

/-- The specification's agreement theorem is the running replicas', across the codec. -/
theorem relative_agreement_of_refines (refines : RelativeRefines) : RelativeAgreement := by
  intro c faulty checked time net reachable size faultBound p q pm qm ph qh
  obtain ⟨spec, specReachable, same⟩ := refines reachable size faultBound
  rcases (same p pm ph).1 with empty | left
  · rw [empty]; exact Or.inl (List.nil_prefix)
  · rcases (same q qm qh).1 with empty | right
    · rw [empty]; exact Or.inr (List.nil_prefix)
    · exact actual_delivered_blocks_compatible specReachable size faultBound pm qm ph qh left right

/-! ## Witnesses -/

/-- Admission, executable, for the pole committee (party 3 faulty, every history checked). -/
def relAllowedB (net : RelNetwork) (receiver : Nat) (input : WireInput) : Bool :=
  decide (receiver < poleConfig.parties) && receiver != 3 &&
  match input with
  | .delivery w | .deliveryAt _ w =>
      decide (w.sender < poleConfig.parties) &&
        (w.sender == 3 || (net.sent w.sender).any fun entry => decide (entry.2 = w))
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
      exact ⟨entry, member, Or.inl (of_decide_eq_true same)⟩
  | checked height records => exact ⟨of_decide_eq_true rest, trivial⟩
  | tick _ | offer _ | poll => trivial

def relRun : RelNetwork → List (Nat × WireInput) → Option RelNetwork
  | net, [] => some net
  | net, (party, input) :: rest =>
      if relAllowedB net party input then relRun (relAdvance poleConfig net party input) rest else none

theorem relRun_reachable {time : Nat} (net result : RelNetwork) (inputs : List (Nat × WireInput))
    (reachable : RelReachable poleConfig poleFaulty (fun _ _ => True) time net)
    (run : relRun net inputs = some result) :
    RelReachable poleConfig poleFaulty (fun _ _ => True) time result := by
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
      poleSchedule fuel (pending.foldl (fun net step => relAdvance poleConfig net step.1 step.2) net)
        (done ++ pending)

def poleInputs : List (Nat × WireInput) :=
  let checks : List (Nat × WireInput) := [0, 1, 2].map fun party => (party, .checked 0 [[7]])
  (poleSchedule 16
    (checks.foldl (fun net step => relAdvance poleConfig net step.1 step.2) (relInitial poleConfig 0))
    checks).1

/-- Premise inhabitation: the schedule is admitted from the real start, and the three
correct replicas have each committed `[[7]]` and moved their origin to height 1. -/
theorem relNet_run :
    ((relRun (relInitial poleConfig 0) poleInputs).map fun net =>
      [0, 1, 2].map fun party => (net.chain party, (net.replica party).height,
        (net.replica party).core.committedTip)) =
      some [([[7]], 1, []), ([[7]], 1, []), ([[7]], 1, [])] := by
  native_decide

theorem relNet_reachable :
    ∃ net, RelReachable poleConfig poleFaulty (fun _ _ => True) 0 net ∧
      ∀ party, party < 3 → net.chain party = [[7]] := by
  rcases run : relRun (relInitial poleConfig 0) poleInputs with _ | net
  · have executed := relNet_run
    rw [run] at executed
    simp at executed
  · refine ⟨net, relRun_reachable _ net _ .initial run, ?_⟩
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

/-- Teeth: the conclusion is not idle. A network whose replicas 0 and 1 hold `[[1]]` and
`[[2]]` does not agree. -/
theorem conflict_not_agreement :
    ¬ Agrees poleConfig poleFaulty
      { replica := fun party => (Replica.start poleConfig party 0).drain.2
        chain := fun party => if party = 0 then [[1]] else [[2]]
        sent := fun _ => [] } := by
  intro agrees
  have conflict := agrees 0 1 (by decide) (by decide) (by decide) (by decide)
  simp at conflict

#assert_axioms relative_agreement_of_refines relAllowedB_sound relRun_reachable conflict_not_agreement
#assert_axioms above_denotes decode_encode decode_ahead strip_denotes strip_conflict holdFar_unique
#assert_compiled relNet_run
#assert_compiled relNet_reachable
#assert_compiled GenericSimplexRelative.same_run_both_engines
#assert_compiled GenericSimplexRelative.recovery
#assert_compiled GenericSimplexRelative.delivery_policy
#assert_compiled GenericSimplexRelative.fixed_origin_grows

end Minidregg.Verify.GenericSimplexRelativeReach
