/-
Poles for the slot-to-slot atoms `eqSlots`/`leSlots` through the one compiler. The field
`ZMod 17` and width 2 are proof fixtures, as in `PredCompileOrderWitness`.

The runner law binds an output to an observed input (`total/after` equals the observed
ledger `sum/after`) and caps spending by a budget slot. The story law is the motivating
`at == 4 ⇒ has/key == need/key` written with a slot-to-slot atom.

Slot names are short so the kernel evaluates the emitted systems quickly; they stand for
`out` = `resource/field/total/after`, `in` = `joint/target/ledger/resource/field/sum/after`,
`spent`/`cap` = `resource/field/{spent,budget}/after`, `at` = `player/S/at/after`,
`key` = `player/S/has/key/after`, `need` = the scene's required key. The atoms read slot names
opaquely, so nothing depends on the spelling.
-/
import Compiler.PredCompile

namespace Minidregg.Compiler.SlotFoldWitness

open Minidregg.Pred (Pred State)

private instance : Fact (Nat.Prime 17) := ⟨by decide⟩

def profile : CompilerProfile := .scalar 2

theorem profile_admissible : profile.Admissible (ZMod 17) :=
  PredOrder.noWrap_zmod (by decide)

/-- Output bound to its observed input, and spending capped by a budget slot. -/
def runnerLaw : Pred := Pred.all
  [.eqSlots "out" "in",
   .leSlots "spent" "cap"]

def before : State := ⟨[("out", 0)]⟩

/-- The runner wrote the input's current sum and stayed within budget. -/
def fresh : State := ⟨[("out", 5),
  ("in", 5),
  ("spent", 2), ("cap", 3)]⟩

/-- The runner wrote a stale answer: the observed sum moved to 5, the output says 4. -/
def stale : State := ⟨[("out", 4),
  ("in", 5),
  ("spent", 2), ("cap", 3)]⟩

/-- The runner overspent: 4 against a budget of 3. -/
def overspent : State := ⟨[("out", 5),
  ("in", 5),
  ("spent", 4), ("cap", 3)]⟩

/-- The input was not observed: the joint slot is absent, so equality fails closed. -/
def unobserved : State := ⟨[("out", 0),
  ("spent", 2), ("cap", 3)]⟩

theorem runner_source_poles :
    Minidregg.Pred.eval runnerLaw before fresh = true ∧
    Minidregg.Pred.eval runnerLaw before stale = false ∧
    Minidregg.Pred.eval runnerLaw before overspent = false ∧
    Minidregg.Pred.eval runnerLaw before unobserved = false := by decide

theorem runner_support : supported profile runnerLaw = true := by decide

/-- The emitted constraints and executable witness compute to acceptance on the fresh step. -/
theorem runner_fresh_accepts :
    systemAccepts (stepAsg before fresh (wit profile (F := ZMod 17) runnerLaw before fresh))
      (lower profile runnerLaw) := by decide

/-- A refused step is refused for every auxiliary assignment, by the general soundness theorem. -/
theorem refused_for_every_witness (after : State)
    (hinj : castInjOn (ZMod 17) (intsOf runnerLaw before after))
    (hrange : inputsInRange profile runnerLaw before after = true)
    (hfalse : Minidregg.Pred.eval runnerLaw before after = false)
    (A : List Nat → Nat → ZMod 17) :
    ¬ systemAccepts (stepAsg before after A) (lower profile runnerLaw) := by
  intro accepted
  have holds := lower_sound profile profile_admissible hinj runner_support hrange accepted
  rw [hfalse] at holds
  contradiction

theorem runner_stale_refused (A : List Nat → Nat → ZMod 17) :
    ¬ systemAccepts (stepAsg before stale A) (lower profile runnerLaw) :=
  refused_for_every_witness stale (by decide) (by decide) (by decide) A

theorem runner_overspent_refused (A : List Nat → Nat → ZMod 17) :
    ¬ systemAccepts (stepAsg before overspent A) (lower profile runnerLaw) :=
  refused_for_every_witness overspent (by decide) (by decide) (by decide) A

theorem runner_unobserved_refused (A : List Nat → Nat → ZMod 17) :
    ¬ systemAccepts (stepAsg before unobserved A) (lower profile runnerLaw) :=
  refused_for_every_witness unobserved (by decide) (by decide) (by decide) A

/-- A witness for the fresh step does not carry over to the stale one. -/
theorem fresh_witness_on_stale_refused :
    ¬ systemAccepts (stepAsg before stale (wit profile (F := ZMod 17) runnerLaw before fresh))
      (lower profile runnerLaw) := by decide

/-- Story movement gated on an item: at scene 4 the player must hold the needed key. -/
def storyLaw : Pred := Pred.any
  [.not (.eq "at" 4), .eqSlots "key" "need"]

def atGateWithKey : State :=
  ⟨[("at", 4), ("key", 1), ("need", 1)]⟩
def atGateWithoutKey : State :=
  ⟨[("at", 4), ("key", 0), ("need", 1)]⟩
def elsewhereWithoutKey : State :=
  ⟨[("at", 3), ("key", 0), ("need", 1)]⟩

theorem story_source_poles :
    Minidregg.Pred.eval storyLaw before atGateWithKey = true ∧
    Minidregg.Pred.eval storyLaw before atGateWithoutKey = false ∧
    Minidregg.Pred.eval storyLaw before elsewhereWithoutKey = true := by decide

theorem story_with_key_accepts :
    systemAccepts
      (stepAsg before atGateWithKey (wit profile (F := ZMod 17) storyLaw before atGateWithKey))
      (lower profile storyLaw) := by decide

theorem story_without_key_refused (A : List Nat → Nat → ZMod 17) :
    ¬ systemAccepts (stepAsg before atGateWithoutKey A) (lower profile storyLaw) := by
  intro accepted
  have holds := lower_sound profile profile_admissible
    (by decide : castInjOn (ZMod 17) (intsOf storyLaw before atGateWithoutKey))
    (by decide) (by decide) accepted
  have hfalse : Minidregg.Pred.eval storyLaw before atGateWithoutKey = false := by decide
  rw [hfalse] at holds
  contradiction

/-- The explicit disabled profile refuses `leSlots` on every assignment. -/
theorem disabled_refuses_leSlots (A : List Nat → Nat → ZMod 17) :
    ¬ systemAccepts (stepAsg before fresh A)
      (lower CompilerProfile.disabled (.leSlots "spent"
        "cap")) :=
  lower_leSlots_disabled_refuses _ _ _

/-- info: 'Minidregg.Compiler.SlotFoldWitness.runner_fresh_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runner_fresh_accepts
/-- info: 'Minidregg.Compiler.SlotFoldWitness.runner_stale_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runner_stale_refused
/-- info: 'Minidregg.Compiler.SlotFoldWitness.runner_overspent_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runner_overspent_refused
/-- info: 'Minidregg.Compiler.SlotFoldWitness.runner_unobserved_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runner_unobserved_refused
/-- info: 'Minidregg.Compiler.SlotFoldWitness.story_with_key_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms story_with_key_accepts
/-- info: 'Minidregg.Compiler.SlotFoldWitness.story_without_key_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms story_without_key_refused

end Minidregg.Compiler.SlotFoldWitness
