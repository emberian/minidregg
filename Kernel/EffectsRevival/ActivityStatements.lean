/-
# `Kernel/EffectsRevival/ActivityStatements.lean` — an activity effect refuses at two levels, STATED

The review's §6 hazard for migration step 2 (`docs/EFFECTS-REVIVAL.md` §5), stated before
that step.  A yield that asks the kernel for a transfer can be refused at two levels:

* **the turn**: the yield's own guards (patience, the deadline's width, the declared-state
  write, the effect protocol) refuse, and `commitYield` returns `.error`, so the turn is
  rejected, by name;
* **the effect**: the guards pass and `transferVerdict` refuses the transfer (`reserved`,
  `closed`, `unfunded`).  `commitYield` then returns `.ok`: the turn is ACCEPTED, the await
  records the refusal as its verdict (`.performed (.refused reason)`), and nothing else is
  committed (no state write, no posts, no transfer).

An engine migration whose declared transfer semantics maps the effect-level refusal to the
declaration's `refused` (a turn rejection) changes the deployed semantics.  `TwoLevels` is a
predicate on ANY candidate yield judgment, so the step-2 declaration's derived executor
(projected to a `YieldCommit`) is checked against it directly; today's `commitYield` is its
satisfiable pole, and the collapsed judgment is refuted.

This file proves nothing; the proofs follow the auditor's verdict.
-/
module

public import Effects.Revival.Engine
public import Kernel.ObjectiveActivity

@[expose] public section

namespace Minidregg.Effects.Revival

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ObjectiveActivity
open Minidregg.Theory.ObjectiveBendDemandData (Data)
open Minidregg.Theory.CanonicalResourceKernel (AccountId)

set_option autoImplicit false

/-- Everything a yield's judgment reads (`commitYield`'s arguments). -/
structure YieldInput where
  rootBytes : List UInt8 → Digest
  config : Config
  snapshot : ObjectiveActivity.Snapshot rootBytes
  height : Nat
  transaction : TransactionId
  cell : CellId
  object : CellId
  generation : Nat
  checkpoint : Digest
  current : Option ObjectState
  viewed : Bool
  plan : PlanAwait
  funds : Funds
  reserve : Await → Nat

/-- Today's judgment: the kernel's `commitYield`. -/
def YieldInput.reference (i : YieldInput) : Except Refusal YieldCommit :=
  commitYield i.config i.snapshot i.height i.transaction i.cell i.object i.generation i.checkpoint
    i.current i.viewed i.plan i.funds i.reserve

/-- The await a yield opens when the kernel decides its effect with `verdict`. -/
def YieldInput.performedAwait (i : YieldInput) (verdict : Verdict) : Await :=
  ⟨awaitId i.cell i.generation i.checkpoint, .performed verdict, i.height + i.plan.patience, i.height⟩

/-- **An effect-level refusal**: the yield's turn-level guards pass (patience, the deadline's
width, the declared-state write, the effect protocol), the plan asks for a transfer, and the
verdict refuses it. -/
def YieldInput.TransferRefused (i : YieldInput) (reason : EffectRefusal) : Prop :=
  ¬ (i.plan.patience = 0 ∨ i.config.maxPatience < i.plan.patience) ∧
  ¬ (256 ^ 8 ≤ i.height + i.plan.patience) ∧
  i.funds.effects = true ∧
  ∃ (recipient : AccountId) (amount : Nat) (written : Option StateWritten),
    i.plan.source = .performed (.transfer recipient amount) ∧
    stateWrite i.config i.snapshot i.object i.current i.viewed i.plan.write = .ok written ∧
    transferVerdict i.config i.funds (i.reserve (i.performedAwait .settled)) written recipient amount =
      .refused reason

/-- **`candidate` keeps the two levels.**
* `verdict`: an effect-level refusal is an ACCEPTED yield whose await records the refusal,
  committing no state write, no posts and no transfer;
* `ok`: every yield today's judgment admits is admitted with the same commit (a settled
  transfer is not turned into a rejection, the opposite collapse);
* `turn`: every refusal of today's judgment is still a refusal of the turn, under the same
  name. -/
structure TwoLevels (candidate : YieldInput → Except Refusal YieldCommit) : Prop where
  verdict : ∀ i reason, i.TransferRefused reason →
    candidate i = .ok ⟨i.performedAwait (.refused reason), none, [], none⟩
  ok : ∀ i c, i.reference = .ok c → candidate i = .ok c
  turn : ∀ i r, i.reference = .error r → candidate i = .error r

/-- **Satisfiable.**  Today's kernel keeps the two levels. -/
def TwoLevelsSatisfiable : Prop := TwoLevels YieldInput.reference

/-- **Premise inhabitation.**  An effect-level refusal exists (the `verdict` clause is not
vacuous). -/
def TwoLevelsPremise : Prop := ∃ (i : YieldInput) (reason : EffectRefusal), i.TransferRefused reason

/-- The collapsed judgment: an effect-level refusal becomes a turn rejection (the migration
the review warns against). -/
def collapsedJudgment (i : YieldInput) : Except Refusal YieldCommit :=
  match i.reference with
  | .ok committed =>
    match committed.await.source with
    | .performed (.refused reason) => .error (.plan s!"transfer refused: {reprStr reason}")
    | _ => .ok committed
  | .error r => .error r

/-- **Teeth.**  The collapsed judgment does not keep the two levels. -/
def TwoLevelsTeeth : Prop := ¬ TwoLevels collapsedJudgment

end Minidregg.Effects.Revival
