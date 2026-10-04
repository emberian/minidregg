import Kernel.GenericSimplexStructure
import Kernel.GenericSimplexLawfulBEq

namespace Minidregg.Kernel.GenericSimplexWitnesses
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GeneralSimplexReachability
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

abbrev Schedule := List (Nat × Input)

def runSchedule (c : Config) (faulty : Finset Nat) : Network → Schedule → Network
  | net, [] => net
  | net, (party,input)::rest => runSchedule c faulty (advance c faulty net party input) rest

def AllowedSchedule (c : Config) (faulty : Finset Nat)
    (checked : Network → Nat → Block → Prop) : Network → Schedule → Prop
  | _, [] => True
  | net, (party,input)::rest => AllowedInput c faulty checked net party input ∧
      AllowedSchedule c faulty checked (advance c faulty net party input) rest

theorem runSchedule_reachable {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {initialTime : Nat} {net : Network}
    (reachable : Reachable c faulty checked initialTime net) (schedule : Schedule)
    (allowed : AllowedSchedule c faulty checked net schedule) :
    Reachable c faulty checked initialTime (runSchedule c faulty net schedule) := by
  induction schedule generalizing net with
  | nil => exact reachable
  | cons action rest ih =>
    rcases action with ⟨party,input⟩
    exact ih (.next reachable party input allowed.1) allowed.2

def config : Config := ⟨4,1,10,4,0⟩
def baseBlock : Block := [[]]
def otherBlock : Block := [[1]]
def checked (_ : Network) (_ : Nat) (block : Block) : Prop := block = otherBlock


def inputDecision (c : Config) (faulty : Finset Nat) (net : Network) (party : Nat) (input : Input) :
    Decidable (AllowedInput c faulty checked net party input) := by
  cases input <;> unfold AllowedInput <;> dsimp only [authenticDelivery, checked] <;> infer_instance

instance scheduleDecision (c : Config) (faulty : Finset Nat) (net : Network) (schedule : Schedule) :
    Decidable (AllowedSchedule c faulty checked net schedule) :=
  match schedule with
  | [] => isTrue True.intro
  | (party,input)::rest =>
      @instDecidableAnd _ _ (inputDecision c faulty net party input)
        (scheduleDecision c faulty (advance c faulty net party input) rest)

def deliver (receiver sender : Nat) (kind : Kind) (block : Block) : Nat × Input :=
  (receiver, .delivery ⟨sender,1,kind,some block⟩)

def honestFaulty : Finset Nat := {3}
def honestSchedule : Schedule := [
  deliver 1 0 .propose baseBlock, deliver 2 0 .propose baseBlock,
  deliver 0 1 .vote baseBlock, deliver 0 2 .vote baseBlock,
  deliver 1 0 .vote baseBlock, deliver 1 2 .vote baseBlock,
  deliver 2 0 .vote baseBlock, deliver 2 1 .vote baseBlock,
  deliver 0 1 .commit baseBlock, deliver 0 2 .commit baseBlock]
def honestRun : Network := runSchedule config honestFaulty (initial config 0) honestSchedule

/-- Three honest parties actually exchange proposals/votes/commits while the
fourth member is faulty and silent. This witnesses the executable assumptions. -/
theorem honest_schedule_allowed :
    AllowedSchedule config honestFaulty checked (initial config 0) honestSchedule := by decide

theorem honest_run_reachable : Reachable config honestFaulty checked 0 honestRun :=
  runSchedule_reachable .initial honestSchedule honest_schedule_allowed

theorem honest_run_commits :
    (.commit 0 1 baseBlock : AuditEvent) ∈ honestRun.audit ∧
      baseBlock ∈ (honestRun.localState 0).delivered := by decide

theorem honest_fault_bound : honestFaulty.card ≤ config.faults := by decide

def excessFaulty : Finset Nat := {2,3}
def hostileSchedule : Schedule := [
  (1,.checked otherBlock),
  deliver 1 2 .vote otherBlock, deliver 1 3 .vote otherBlock,
  deliver 1 2 .candidate otherBlock, deliver 1 3 .candidate otherBlock,
  deliver 1 2 .ready otherBlock, deliver 1 3 .ready otherBlock,
  deliver 1 2 .commit otherBlock, deliver 1 3 .commit otherBlock,
  deliver 0 2 .vote baseBlock, deliver 0 3 .vote baseBlock,
  deliver 0 2 .commit baseBlock, deliver 0 3 .commit baseBlock]
def hostileRun : Network := runSchedule config excessFaulty (initial config 0) hostileSchedule

/-- Exactly f+1 Byzantine parties can give honest parties conflicting quorums.
Every honest action still comes from the same executable engine. -/
theorem hostile_schedule_allowed :
    AllowedSchedule config excessFaulty checked (initial config 0) hostileSchedule := by decide

theorem hostile_run_reachable : Reachable config excessFaulty checked 0 hostileRun :=
  runSchedule_reachable .initial hostileSchedule hostile_schedule_allowed

theorem hostile_run_conflicting_commits :
    (.commit 0 1 baseBlock : AuditEvent) ∈ hostileRun.audit ∧
    (.commit 1 1 otherBlock : AuditEvent) ∈ hostileRun.audit ∧
    ¬baseBlock.IsPrefix otherBlock ∧ ¬otherBlock.IsPrefix baseBlock := by decide

theorem hostile_exactly_one_fault_over_bound :
    excessFaulty.card = config.faults+1 ∧ 0 ∉ excessFaulty ∧ 1 ∉ excessFaulty := by decide

#assert_axioms runSchedule_reachable
#assert_axioms honest_schedule_allowed
#assert_axioms honest_run_reachable
#assert_axioms honest_run_commits
#assert_axioms honest_fault_bound
#assert_axioms hostile_schedule_allowed
#assert_axioms hostile_run_reachable
#assert_axioms hostile_run_conflicting_commits
#assert_axioms hostile_exactly_one_fault_over_bound
end Minidregg.Kernel.GenericSimplexWitnesses
