import Kernel.GenericSimplexObservationSafety
import Theory.AssertCompiled
import Verify.GenericSimplexFloorStatements

/-! Ties the executed controls of `Verify.GenericSimplexJumpStarvation` to the proof
closure's own vocabulary.

* `allowed_eq_allowedB`: the admission test those runs used IS `allowedB poleConfig
  poleFaulty` on the network of their states, so every input they applied satisfies the
  real `AllowedInput` (`allowed_sound`), whichever step rule produced the states.
* `reachRun_runChecked`: the concrete input list of a three-round `.main` run, fed to the
  real `runChecked` from the real `initial`, is admitted and ends in the same honest states
  (kernel-checked: this one is a premise of `reachRun_reachable`, so the kernel is the
  point, and three rounds cost it seconds); hence `reachRun_reachable`, and
  `settled_premise_inhabited`.
* `SettledBelowFrontier`, `EventualCommit`: statements, no proofs.
* The pins: `#assert_axioms` on what the kernel checked, `#assert_compiled` on the executed
  controls of `GenericSimplexJumpStarvation` and `GenericSimplexFloorStatements` that are
  compiled evaluations. -/
namespace Minidregg.Verify.GenericSimplexJumpReach
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GeneralSimplexReachability
open Minidregg.Kernel.GenericSimplexObservationSafety
open Minidregg.Verify.GenericSimplexJumpStarvation
set_option autoImplicit false

/-- The proof closure's network over a run's states. `allowedB` reads only `localState`. -/
def toNetwork (net : Net) : Network := ⟨fun party => net.states[party]!, []⟩

theorem cfg_eq_poleConfig : cfg = poleConfig := rfl

theorem allowed_eq_allowedB (net : Net) (receiver : Nat) (input : Input) :
    allowed net receiver input =
      allowedB poleConfig poleFaulty (toNetwork net) receiver input := by
  rw [Bool.eq_iff_iff]
  cases input <;>
    simp [allowed, allowedB, toNetwork, cfg, poleConfig, poleFaulty]
  all_goals first
    | (intro _; congr)
    | (constructor <;> rintro ⟨left, enrolled, source⟩ <;> refine ⟨left, enrolled, ?_⟩ <;>
        rcases source with byz | sent <;>
        first
          | exact Or.inl byz
          | exact Or.inr (of_decide_eq_true sent)
          | exact Or.inr (decide_eq_true sent))

/-- Every input the executed runs applied satisfies the real `AllowedInput`. -/
theorem allowed_sound {net : Net} {receiver : Nat} {input : Input}
    (ok : allowed net receiver input = true) :
    AllowedInput poleConfig poleFaulty poleChecked (toNetwork net) receiver input :=
  allowedB_sound (by rw [← allowed_eq_allowedB]; exact ok)

/-- The three-round `.main` run through the real `runChecked`: admitted, same honest
states. -/
theorem reachRun_runChecked :
    ((runChecked poleConfig poleFaulty (initial poleConfig 0) reachRun.schedule).map
      fun net => [0, 1, 2].map net.localState) = some (honestStates reachRun) := by
  decide +kernel

theorem reachRun_reachable :
    ∃ net, Reachable poleConfig poleFaulty poleChecked 0 net ∧
      [0, 1, 2].map net.localState = honestStates reachRun := by
  rcases run : runChecked poleConfig poleFaulty (initial poleConfig 0) reachRun.schedule with _ | net
  · have admitted := reachRun_runChecked
    rw [run] at admitted
    simp at admitted
  · refine ⟨net, runChecked_reachable _ _ net .initial run, ?_⟩
    have admitted := reachRun_runChecked
    rw [run] at admitted
    simpa using admitted

/-- The run's honest replicas are past view 1 (views 4, 2, 3) and have committed it. -/
theorem reachRun_frontier :
    ((honestStates reachRun).all fun s =>
      decide (1 < s.current) && (viewAt s 1).committed.isSome) = true := by
  decide +kernel

/-- Premise inhabitation for `SettledBelowFrontier`: a reachable network of the pole
committee in which honest party 0 has passed view 1. -/
theorem settled_premise_inhabited :
    ∃ net, Reachable poleConfig poleFaulty poleChecked 0 net ∧
      1 < (net.localState 0).current := by
  obtain ⟨net, reachable, states⟩ := reachRun_reachable
  refine ⟨net, reachable, ?_⟩
  have frontier := reachRun_frontier
  rw [← states] at frontier
  simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, decide_eq_true_eq] at frontier
  omega

/-- STATEMENT (no proof). Every view an honest replica has passed is prepared or disabled
at some honest replica, or lies at or below a view some honest replica committed.

satisfiable / premise-inhabitation: `settled_premise_inhabited`, `poleNet_reachable`.
teeth: a step that enters a view on an unprepared hint (PR #18's "unprepared hint" mutant). -/
def SettledBelowFrontier : Prop :=
  ∀ {c : Config} {faulty : Finset Nat} {checked : Network → Nat → Block → Prop}
    {time : Nat} {net : Network},
    Reachable c faulty checked time net →
    c.parties = 3 * c.faults + 1 → faulty.card ≤ c.faults →
    ∀ p v, p < c.parties → p ∉ faulty → 0 < v → v < (net.localState p).current →
      ∃ q, q < c.parties ∧ q ∉ faulty ∧
        ((viewAt (net.localState q) v).prepared ≠ [] ∨
         (viewAt (net.localState q) v).disabled = true ∨
         ∃ w, v ≤ w ∧ ((viewAt (net.localState q) w).committed).isSome = true)

/-! ## `eventual_commit`: a statement only

Nothing below is proved, and liveness is not a theorem for this engine under any timer
(docs/GENERIC-SIMPLEX-NATIVE.md). This is the first written form of the progress claim, for
its statement audit. Its premises have no executed inhabitant: an `Execution` is infinite.
The finite facts that bear on it are `GenericSimplexJumpStarvation.main_commits_same_policy`
(commits under an adversarial schedule) and `stranded_without_commit_transfer` (what the
`CommitTransfer` premise is for). -/

/-- An infinite run of the real network: one admitted input per index, with the driver's
clock. Ticks and timed deliveries carry that clock. -/
structure Execution (c : Config) (faulty : Finset Nat)
    (checked : Network → Nat → Block → Prop) where
  net : Nat → Network
  party : Nat → Nat
  input : Nat → Input
  time : Nat → Nat
  start : net 0 = initial c (time 0)
  admitted : ∀ i, AllowedInput c faulty checked (net i) (party i) (input i)
  next : ∀ i, net (i + 1) = advance c faulty (net i) (party i) (input i)
  monotone : ∀ i, time i ≤ time (i + 1)
  unbounded : ∀ t, ∃ i, t ≤ time i
  tickClock : ∀ i now, input i = .tick now → now = time i
  deliveryClock : ∀ i now m, input i = .deliveryAt now m → now = time i

def Honest (c : Config) (faulty : Finset Nat) (p : Nat) : Prop := p < c.parties ∧ p ∉ faulty

variable {c : Config} {faulty : Finset Nat} {checked : Network → Nat → Block → Prop}

def Execution.state (e : Execution c faulty checked) (i p : Nat) : State := (e.net i).localState p

/-- Input `j` hands message `m` to party `q`. -/
def Execution.delivers (e : Execution c faulty checked) (j q : Nat) (m : Message) : Prop :=
  e.party j = q ∧ (e.input j = .delivery m ∨ ∃ now, e.input j = .deliveryAt now m)

/-- Partial synchrony: after `gst`, every message an honest replica has sent reaches every
other honest replica within `delta`, and every honest replica is ticked at least every
`delta` with the current clock. -/
structure Synchronous (e : Execution c faulty checked) (gst delta : Nat) : Prop where
  delivery : ∀ i p q m, Honest c faulty p → Honest c faulty q → q ≠ p → m.sender = p →
    AuditEvent.send m ∈ (e.state i p).audit →
    ∃ j, e.time j ≤ max (e.time i) gst + delta ∧ e.delivers j q m
  ticks : ∀ i p, Honest c faulty p →
    ∃ j, i ≤ j ∧ e.time j ≤ e.time i + delta ∧ e.party j = p ∧ e.input j = .tick (e.time j)

/-- Commit-evidence transfer: when an honest replica commits a view, every COMMIT message
it counted for that block reaches every other honest replica within `delta` (after `gst`).
Natively these are the COMMITs a peer owes a member that asks (`Replica.owed`), each with its signer's signature. -/
def CommitTransfer (e : Execution c faulty checked) (gst delta : Nat) : Prop :=
  ∀ i p q v b m, Honest c faulty p → Honest c faulty q → q ≠ p →
    (viewAt (e.state i p) v).committed = some b →
    m ∈ (viewAt (e.state i p) v).received → m.kind = .commit → m.value = some b →
    ∃ j, e.time j ≤ max (e.time i) gst + delta ∧ e.delivers j q m

/-- Relay transfer: what an honest replica owes a peer (`State.relay`: its floor evidence,
and its own messages for the views a lagging peer asked about, `serveViews`) reaches that
peer within `delta`. The driver forwards and drains `relay`. -/
def RelayTransfer (e : Execution c faulty checked) (gst delta : Nat) : Prop :=
  ∀ i p q m, Honest c faulty p → Honest c faulty q → (q, m) ∈ (e.state i p).relay →
    ∃ j, e.time j ≤ max (e.time i) gst + delta ∧ e.delivers j q m

/-- Repeat transfer: a message an honest replica puts in its outbox at input `i` (a first
send, or the repeated CANDIDATE(⊥) of a replica stuck past its timeout) is handed to every
other honest replica after `i`, within `delta`. `Synchronous.delivery` alone does not say
this: one early delivery of a message discharges it for every later index. -/
def RepeatTransfer (e : Execution c faulty checked) (gst delta : Nat) : Prop :=
  ∀ i p q m, Honest c faulty p → Honest c faulty q → q ≠ p →
    m ∈ (e.state (i + 1) p).outbox.drop (e.state i p).outbox.length →
    ∃ j, i < j ∧ e.time j ≤ max (e.time i) gst + delta ∧ e.delivers j q m

/-- The source-check premise, as the controller's contract for one payload: from index `i`
on, every honest replica that has not committed the payload holds it as an offer that is
valid on top of its current best parent. -/
def Pending (e : Execution c faulty checked) (i : Nat) (payload : Bytes) : Prop :=
  ∀ j p, i ≤ j → Honest c faulty p → payload ∉ (e.state j p).committedTip →
    payload ∈ (e.state j p).offers ∧
      validBlock (e.state j p) (bestParent (e.state j p) ++ [payload]) = true

/-- STATEMENT `eventual_commit` (no proof). Scope, all in the statement: a static committee
of n = 3f+1 with at most f faulty; delays at most `delta` after `gst`; the capped timer at
least `7 * delta`; commit-evidence transfer; relay and repeat transfer (a replica keeps
no record above its horizon, so one that fell behind recovers only through its repeated
CANDIDATE(⊥) and the peers' answers in `relay`); the payload kept offered and checked. Then
there is a bound, uniform in the execution, within which every honest replica has
committed the payload.

satisfiable / premise-inhabitation: NOT executed (an `Execution` is infinite). teeth: the
`CommitTransfer` premise is not idle (`stranded_without_commit_transfer`), nor is
`RelayTransfer` (`GenericSimplexWindow`: `caughtUp true` stays behind); with PR #18's
prepared jump in the step the conclusion fails on a schedule of this shape
(`pr_jump_starves_commit` shows its first twelve views). -/
def EventualCommit : Prop :=
  ∃ bound : Nat, ∀ (c : Config) (faulty : Finset Nat)
    (checked : Network → Nat → Block → Prop) (e : Execution c faulty checked)
    (gst delta i : Nat) (payload : Bytes),
    c.wellFormed = true → faulty.card ≤ c.faults →
    7 * delta ≤ c.timeout * 2 ^ c.backoffCap →
    Synchronous e gst delta → CommitTransfer e gst delta → RelayTransfer e gst delta →
    RepeatTransfer e gst delta → Pending e i payload →
    ∃ j, e.time j ≤ max (e.time i) gst + bound * c.parties * (c.timeout * 2 ^ c.backoffCap) ∧
      ∀ p, Honest c faulty p → payload ∈ (e.state j p).committedTip

#assert_axioms allowed_eq_allowedB allowed_sound reachRun_runChecked reachRun_reachable
  reachRun_frontier settled_premise_inhabited
#assert_axioms stepV_main startV_main
#assert_axioms GenericSimplexFloorStatements.lagging_floor_disagrees
  GenericSimplexFloorStatements.floor_refuses_executed
  GenericSimplexFloorStatements.erasure_executed
  GenericSimplexFloorStatements.forgotten_floor_observable
#assert_compiled pr_jump_starves_commit
#assert_compiled main_commits_same_policy
#assert_compiled late_vote_jump_commits_same_policy
#assert_compiled forgotten_floor_halts
#assert_compiled stranding_ends_with_floor_evidence
#assert_compiled GenericSimplexFloorStatements.floor_agrees_executed

end Minidregg.Verify.GenericSimplexJumpReach
