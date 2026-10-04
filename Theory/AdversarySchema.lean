/-
# Theory.AdversarySchema — `GovernedDynamics`, the top-level shape of a security statement

Port of the candidate-independent half of breadstuffs
`metatheory/Metatheory/Adversary/Schema.lean` (ATLAS §3 item 2): §1 (the schema and its one
consumer) and §5 (anti-vacuity). A security statement is a dynamics driven by an adversarial
`Control`, with an `accept` predicate and a safety `invariant`, such that for every control
an accepted outcome satisfies the invariant.

NOT ported, deliberately: the ancestor's two instances. `polisDynamics` rides
`Polis.polis_safety` (whose "one theorem" unification is a shape identity, R2-4 §3), and
`circuitDynamics` rides `lightclient_unfoolable`, vacuous at BabyBear (the apex's
`CommitSurface`-injective floor). Mini instances are written against Mini's own dynamics.

Changes from the ancestor: namespace (`Metatheory.Adversary` → `Minidregg.Theory.Adversary`);
explicit `universe u v`; axiom pins are `#guard_msgs` over `#print axioms` with the
ancestor's exact output.
-/
import Mathlib.Logic.IsEmpty.Basic

namespace Minidregg.Theory.Adversary

set_option autoImplicit false

universe u v

/-! ## §1. The abstract governance property + the schema. -/

/-- **`GovernedProperty run accept invariant`** — for EVERY control `c`, if the outcome
`run c` is accepted, it satisfies the invariant. A real predicate on
`(run, accept, invariant)`: FALSE for some tuples (`broken_dynamics_not_governed`). -/
def GovernedProperty {C : Type u} {O : Type v}
    (run : C → O) (accept : O → Prop) (invariant : O → Prop) : Prop :=
  ∀ c, accept (run c) → invariant (run c)

/-- **`GovernedDynamics` — the single abstract schema.** A dynamics driven by an
adversarial `Control`, producing an `Outcome`, with an `accept` predicate and a safety
`invariant`, PROVED to satisfy `GovernedProperty`. -/
structure GovernedDynamics where
  /-- the adversary's control surface. -/
  Control : Type u
  /-- what a control produces (a run result / a verified claim). -/
  Outcome : Type v
  /-- how a control drives the dynamics to an outcome. -/
  run : Control → Outcome
  /-- which outcomes are ACCEPTED / reached (the admission floor). -/
  accept : Outcome → Prop
  /-- the safety / genuineness the accepted outcome must satisfy. -/
  invariant : Outcome → Prop
  /-- **the governance proof** — no control drives an accepted outcome out of the invariant. -/
  holds : GovernedProperty run accept invariant

/-- **`governed_holds` — the unified lemma.** For every governed dynamics `D` and every
adversarial control `c`, an accepted outcome satisfies the invariant. -/
theorem governed_holds (D : GovernedDynamics) (c : D.Control)
    (h : D.accept (D.run c)) : D.invariant (D.run c) :=
  D.holds c h

/-! ## §5. Anti-vacuity — the schema carries real content (it is NOT a `P → P`). -/

/-- **(POSITIVE) a non-trivial governed instance.** Accept = "even" (rejects odds),
invariant = "≠ 1" (excludes `1`); `holds` is a real proof. -/
def evenNeqOneDynamics : GovernedDynamics where
  Control := Nat
  Outcome := Nat
  run n := n
  accept n := n % 2 = 0
  invariant n := n ≠ 1
  holds n h := by omega

/-- The positive instance's accept-set genuinely REJECTS: `1` is not accepted. -/
theorem evenNeqOne_accept_nontrivial : ¬ evenNeqOneDynamics.accept (1 : Nat) := by
  show ¬ ((1 : Nat) % 2 = 0); decide

/-- The positive instance's invariant genuinely CONSTRAINS: `1` violates it. -/
theorem evenNeqOne_invariant_nontrivial : ¬ evenNeqOneDynamics.invariant (1 : Nat) := by
  show ¬ ((1 : Nat) ≠ 1); decide

/-- **(NEGATIVE) not every dynamics is governed.** For `run := id`, `accept := True`,
`invariant := (· = true)` over `Bool`, `GovernedProperty` is FALSE. -/
theorem broken_dynamics_not_governed :
    ¬ GovernedProperty (C := Bool) (O := Bool) id (fun _ => True) (fun b => b = true) := by
  intro h
  exact absurd (h false trivial) (by decide)

/-- **The negative, at the schema level.** The `holds` field of any `GovernedDynamics` over
the broken tuple would inhabit an EMPTY type. -/
theorem broken_holds_field_empty :
    IsEmpty (GovernedProperty (C := Bool) (O := Bool) id (fun _ => True) (fun b => b = true)) :=
  ⟨broken_dynamics_not_governed⟩

/-! ## Axiom pins — each is the ancestor's exact `#print axioms` output (2026-10-04 probe of
breadstuffs oleans). -/

/-- info: 'Minidregg.Theory.Adversary.governed_holds' does not depend on any axioms -/
#guard_msgs in #print axioms governed_holds

/-- info: 'Minidregg.Theory.Adversary.evenNeqOne_accept_nontrivial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms evenNeqOne_accept_nontrivial

/-- info: 'Minidregg.Theory.Adversary.evenNeqOne_invariant_nontrivial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms evenNeqOne_invariant_nontrivial

/-- info: 'Minidregg.Theory.Adversary.broken_dynamics_not_governed' does not depend on any axioms -/
#guard_msgs in #print axioms broken_dynamics_not_governed

/-- info: 'Minidregg.Theory.Adversary.broken_holds_field_empty' does not depend on any axioms -/
#guard_msgs in #print axioms broken_holds_field_empty

end Minidregg.Theory.Adversary
