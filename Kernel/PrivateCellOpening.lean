/-
# Kernel.PrivateCellOpening — the zero-knowledge complete selective opening (statement)

Epoch (b)'s prerequisite (docs/RATCHET-LOG-DESIGN.md §3.2, §4 hybrid 2): a reader of a blinded
cell under the private root receives `(root, scope, answer, π)`, where `π` proves in zero
knowledge that `answer` is the COMPLETE projection of the committed store onto the scope. No
sibling digest, path, mask or other-class entry reaches the reader: they stay in the witness.

Statement first (no backend, no circuit yet). Three parts:

* `EmittedOpening`: the circuit's acceptance relation means what the opening needs. Sound: an
  accepted `(statement, circuit witness)` against a root that IS the private root of a gated
  store `S` answers exactly `S`'s authorized projection, or exhibits a scoped node or outer-hash
  collision. Complete: every gated store has an accepted witness for its exact projection, whose
  size is at most `c₀ + c₁ (k + s + 1) 516` (k returned entries, s scope prefixes): a read does
  not grow with the hidden part of the store. `accepts` is to be the compiler-emitted constraint
  system's acceptance (`Compiler/Air`, grown with the hash vocabulary the node digest needs);
  pinning `accepts` to a compiled system is the next statement, once that vocabulary is chosen.
* `ProofSystem`, `Complete`, `SoundUpTo`, `MultiTheoremZK`: a non-interactive proof system with
  fresh coins per proof, adaptive multi-theorem zero knowledge on true statements (the adversary
  chooses each next statement and witness from the proofs so far; the simulator sees only the
  statement), and soundness up to a named bad event (the backend's extraction/soundness error).
* `SelectiveOpening`: a circuit and a backend for it; `selectiveOpening_exact` composes them: an
  honest opening verifies, and an accepted one answers exactly the committed store's projection,
  or the backend's bad event, or a scoped collision.

ATLAS fields:
* satisfiable: `Ideal.system` (proofs carry nothing, the verifier decides the relation) meets
  `Complete`, `SoundUpTo` with no bad event and `MultiTheoremZK` at gap 0 (`Ideal.complete`,
  `Ideal.sound`, `Ideal.zk`);
* teeth: `reveal_refuted`: a system whose proof is its witness is not zero knowledge at any gap
  below one half, against the two adversaries choosing between two witnesses of one statement;
* premise inhabitation: `honest_statement`: every gated store's exact projection is a statement
  of its root.
-/
module

public import Kernel.PrivateCellView
public import Compiler.PrivateCellRoot
public import Theory.FiniteTapeGap
import Theory.AssertAxioms

@[expose] public section

namespace Minidregg.Kernel.PrivateCellOpening

set_option autoImplicit false

open Minidregg.Compiler
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization (CellField Digest)
open Minidregg.Theory.FiniteTapeGap (GapAtMost)
open Minidregg.Kernel.ResourceObservationAdmission (Visible)
open Minidregg.Kernel.PrivateCellView (kindTag storeFits)
open Minidregg.Compiler.PrivateCellIndex (indexEntries)
open Minidregg.Compiler.PrivateCellRoot (privateRoot kindCtx deployedDig paths)

/-! ## A proof system and its properties -/

/-- A non-interactive proof system whose prover draws its coins from a tape: proof `i` of a run
reads `coins t i`, fresh per proof. -/
structure ProofSystem (Stmt Wit Proof : Type) (tapes : Nat) where
  prove : Stmt → Wit → Fin tapes → Nat → Proof
  verify : Stmt → Proof → Bool

/-- An adaptive adversary: the next statement and witness from the proofs so far (or stop), and
a final decision on the proofs it saw. -/
structure Adversary (Stmt Wit Proof : Type) where
  next : List Proof → Option (Stmt × Wit)
  decide : List Proof → Bool

variable {Stmt Wit Proof : Type} {tapes : Nat}

/-- The real run: up to `M` proofs, each on the adversary's next statement and witness. -/
def runReal (sys : ProofSystem Stmt Wit Proof tapes) (A : Adversary Stmt Wit Proof) (t : Fin tapes) :
    Nat → List Proof
  | 0 => []
  | M + 1 =>
      let seen := runReal sys A t M
      match A.next seen with
      | some (x, w) => seen ++ [sys.prove x w t seen.length]
      | none => seen

/-- The simulated run: the simulator sees only each statement. -/
def runSim (sim : Stmt → Fin tapes → Nat → Proof) (A : Adversary Stmt Wit Proof) (t : Fin tapes) :
    Nat → List Proof
  | 0 => []
  | M + 1 =>
      let seen := runSim sim A t M
      match A.next seen with
      | some (x, _) => seen ++ [sim x t seen.length]
      | none => seen

/-- An adversary asks only true statements. -/
def AsksTrue (rel : Stmt → Wit → Prop) (A : Adversary Stmt Wit Proof) : Prop :=
  ∀ seen x w, A.next seen = some (x, w) → rel x w

/-- Honest proofs verify. -/
def Complete (sys : ProofSystem Stmt Wit Proof tapes) (rel : Stmt → Wit → Prop) : Prop :=
  ∀ x w t i, rel x w → sys.verify x (sys.prove x w t i) = true

/-- An accepted proof is of a true statement, or the named bad event happened. -/
def SoundUpTo (sys : ProofSystem Stmt Wit Proof tapes) (rel : Stmt → Wit → Prop)
    (bad : Stmt → Proof → Prop) : Prop :=
  ∀ x π, sys.verify x π = true → (∃ w, rel x w) ∨ bad x π

/-- **Adaptive multi-theorem zero knowledge**: against every budgeted adversary asking at most
`M` true statements, the real and simulated runs are within `num/den`. The simulator gets only
statements; the budget is the efficiency class (the simulator and the reduction's cost live in it). -/
def MultiTheoremZK (sys : ProofSystem Stmt Wit Proof tapes) (sim : Stmt → Fin tapes → Nat → Proof)
    (rel : Stmt → Wit → Prop) (M num den : Nat) (budgeted : Adversary Stmt Wit Proof → Prop) : Prop :=
  ∀ A, budgeted A → AsksTrue rel A →
    GapAtMost tapes num den (fun t => A.decide (runReal sys A t M)) (fun t => A.decide (runSim sim A t M))

/-! ## The deployed opening -/

variable {kind : CanonicalCellRegistry.Kind} (wire : StoreCodec.Wire (CanonicalCellRegistry.layout kind))

/-- What a reader holds: the root, its scope and the answer (each visible address with its
value bytes, in canonical order). -/
structure Statement where
  root : Digest
  fields : Option (Finset CellField)
  answer : List (Address (CanonicalCellRegistry.layout kind) × List UInt8)

/-- The authorized projection of a store: its visible entries as index entries. -/
def projection (fields : Option (Finset CellField)) (store : Store (CanonicalCellRegistry.layout kind)) :
    List (Address (CanonicalCellRegistry.layout kind) × List UInt8) :=
  indexEntries wire (DFinsupp.filter (Visible fields kind) store)

/-- The number of scope prefixes a reader's scope opens. -/
def scopePrefixes (fields : Option (Finset CellField)) : Nat :=
  match fields with
  | none => 1
  | some named => named.card

/-- A collision the circuit's soundness may exhibit: two distinct inputs of the node digest or
of the outer hash with one output, among the nodes and outer inputs of this one comparison
(the store's path nodes and the circuit's revealed nodes; never a global collision). -/
def ScopedCollision (scope : Theory.AuthTrie.NodeIn (Address (CanonicalCellRegistry.layout kind)) (List UInt8) Digest → Prop)
    (outerScope : List UInt8 × Digest → Prop) : Prop :=
  Theory.AuthTrie.CollisionAmong (deployedDig wire) scope ∨
    ∃ a b, a ≠ b ∧ outerScope a ∧ outerScope b ∧
      Compiler.PrivateCellRoot.outerRoot (kindCtx wire) a.1 a.2 =
        Compiler.PrivateCellRoot.outerRoot (kindCtx wire) b.1 b.2

/-- **The emitted circuit means the opening.** `accepts` is the circuit's acceptance relation;
`scopeOf` names, per store and accepted witness, the finite comparison scope a collision is
drawn from. -/
structure EmittedOpening {CWit : Type} (accepts : Statement (kind := kind) → CWit → Bool)
    (witSize : CWit → Nat) (c₀ c₁ : Nat) where
  scopeOf : Store (CanonicalCellRegistry.layout kind) → CWit →
    (Theory.AuthTrie.NodeIn (Address (CanonicalCellRegistry.layout kind)) (List UInt8) Digest → Prop) ×
      (List UInt8 × Digest → Prop)
  /-- Sound: against the private root of a gated store, an accepted answer is that store's
  exact projection, or a scoped collision. -/
  sound : ∀ (st : Statement (kind := kind)) cw (S : Store (CanonicalCellRegistry.layout kind)),
    storeFits wire S = true → st.root = privateRoot wire (kindTag kind) (kindCtx wire) S →
    accepts st cw = true →
      st.answer = projection wire st.fields S ∨ ScopedCollision wire (scopeOf S cw).1 (scopeOf S cw).2
  /-- Complete, with a witness bounded by the answer and the scope, not by the store. -/
  complete : ∀ (S : Store (CanonicalCellRegistry.layout kind)) fields,
    storeFits wire S = true →
    ∃ cw, accepts ⟨privateRoot wire (kindTag kind) (kindCtx wire) S, fields, projection wire fields S⟩ cw = true ∧
      witSize cw ≤ c₀ + c₁ * ((projection wire fields S).length + scopePrefixes fields + 1) * 516

/-- The circuit relation the proof system proves. -/
def circuitRel {CWit : Type} (accepts : Statement (kind := kind) → CWit → Bool) :
    Statement (kind := kind) → CWit → Prop :=
  fun st cw => accepts st cw = true

/-- **The selective opening**: an emitted circuit and a proof system for it, complete, sound up
to its bad event and adaptively multi-theorem zero knowledge at `num/den` for `M` proofs. -/
structure SelectiveOpening (M num den : Nat) where
  CWit : Type
  Proof : Type
  tapes : Nat
  accepts : Statement (kind := kind) → CWit → Bool
  witSize : CWit → Nat
  c₀ : Nat
  c₁ : Nat
  emitted : EmittedOpening wire accepts witSize c₀ c₁
  system : ProofSystem (Statement (kind := kind)) CWit Proof tapes
  simulator : Statement (kind := kind) → Fin tapes → Nat → Proof
  bad : Statement (kind := kind) → Proof → Prop
  budgeted : Adversary (Statement (kind := kind)) CWit Proof → Prop
  complete : Complete system (circuitRel accepts)
  sound : SoundUpTo system (circuitRel accepts) bad
  zk : MultiTheoremZK system simulator (circuitRel accepts) M num den budgeted

/-- **The keystone**: an honest opening of a gated store verifies, and an accepted opening of a
root that is the private root of a gated store answers exactly that store's projection, or the
backend's bad event happened, or the circuit exhibits a scoped collision. -/
theorem selectiveOpening_exact {M num den : Nat} (O : SelectiveOpening wire M num den)
    (S : Store (CanonicalCellRegistry.layout kind)) (gate : storeFits wire S = true) :
    (∀ fields, ∃ cw, ∀ t i,
      O.system.verify ⟨privateRoot wire (kindTag kind) (kindCtx wire) S, fields, projection wire fields S⟩
        (O.system.prove ⟨privateRoot wire (kindTag kind) (kindCtx wire) S, fields, projection wire fields S⟩ cw t i) = true) ∧
    ∀ (st : Statement (kind := kind)) π, st.root = privateRoot wire (kindTag kind) (kindCtx wire) S →
      O.system.verify st π = true →
        st.answer = projection wire st.fields S ∨ O.bad st π ∨
          ∃ cw, ScopedCollision wire (O.emitted.scopeOf S cw).1 (O.emitted.scopeOf S cw).2 := by
  refine ⟨fun fields => ?_, fun st π root accepted => ?_⟩
  · obtain ⟨cw, accepts, _⟩ := O.emitted.complete S fields gate
    exact ⟨cw, fun t i => O.complete _ cw t i accepts⟩
  · rcases O.sound st π accepted with ⟨cw, holds⟩ | bad
    · rcases O.emitted.sound st cw S gate root holds with exact | collision
      · exact Or.inl exact
      · exact Or.inr (Or.inr ⟨cw, collision⟩)
    · exact Or.inr (Or.inl bad)

/-- Premise inhabitation: every gated store's exact projection is a statement of its root, so
`EmittedOpening.complete`'s instances exist. -/
theorem honest_statement (S : Store (CanonicalCellRegistry.layout kind)) (fields : Option (Finset CellField)) :
    (⟨privateRoot wire (kindTag kind) (kindCtx wire) S, fields, projection wire fields S⟩ : Statement (kind := kind)).answer =
      projection wire fields S := rfl

/-! ## The ideal pole and the teeth -/

namespace Ideal

variable {Stmt Wit : Type} (rel : Stmt → Wit → Prop)

/-- Proofs carry nothing; the verifier decides the relation. -/
noncomputable def system : ProofSystem Stmt Wit Unit 1 where
  prove := fun _ _ _ _ => ()
  verify := fun x _ => by classical exact decide (∃ w, rel x w)

theorem complete : Complete (system rel) rel := by
  intro x w t i h
  simp only [system]
  exact decide_eq_true ⟨w, h⟩

theorem sound : SoundUpTo (system rel) rel (fun _ _ => False) := by
  intro x π accepted
  simp only [system, decide_eq_true_eq] at accepted
  exact Or.inl accepted

theorem runReal_eq_runSim (A : Adversary Stmt Wit Unit) (t : Fin 1) :
    ∀ M, runReal (system rel) A t M = runSim (fun _ _ _ => ()) A t M
  | 0 => rfl
  | M + 1 => by
      simp only [runReal, runSim, runReal_eq_runSim A t M]
      cases A.next (runSim (fun _ _ _ => ()) A t M) with
      | none => rfl
      | some p => rfl

theorem zk (M den : Nat) (positive : 0 < den) (budgeted : Adversary Stmt Wit Unit → Prop) :
    MultiTheoremZK (system rel) (fun _ _ _ => ()) rel M 0 den budgeted := by
  intro A _ _
  refine ⟨by decide, positive, ?_, ?_⟩ <;>
    simp [runReal_eq_runSim rel A]

end Ideal

section Teeth

variable {Stmt Wit : Type} [DecidableEq Wit]

theorem count_disjoint {α : Type} (p q : α → Bool) (disjoint : ∀ a, ¬ (p a = true ∧ q a = true)) :
    ∀ l : List α, (l.map p).count true + (l.map q).count true ≤ l.length
  | [] => by simp
  | a :: l => by
      have ih := count_disjoint p q disjoint l
      have := disjoint a
      cases hp : p a <;> cases hq : q a <;> simp_all [List.count_cons] <;> omega

/-- The system whose proof is its witness. -/
def revealSystem (verify : Stmt → Wit → Bool) (tapes : Nat) : ProofSystem Stmt Wit Wit tapes where
  prove := fun _ w _ _ => w
  verify := verify

/-- The adversary asking `x` with witness `w` once, and accepting when the proof is `w`. -/
def askOnce (x : Stmt) (w : Wit) : Adversary Stmt Wit Wit where
  next := fun seen => if seen = [] then some (x, w) else none
  decide := fun seen => seen == [w]

/-- **Teeth**: a system that reveals its witness is not zero knowledge below one half, whenever
one statement has two witnesses, against any budget admitting the two one-query adversaries. -/
theorem reveal_refuted (rel : Stmt → Wit → Prop) (verify : Stmt → Wit → Bool) {tapes num den : Nat}
    (x : Stmt) (w₁ w₂ : Wit) (distinct : w₁ ≠ w₂) (h₁ : rel x w₁) (h₂ : rel x w₂)
    (budgeted : Adversary Stmt Wit Wit → Prop) (admits₁ : budgeted (askOnce x w₁))
    (admits₂ : budgeted (askOnce x w₂)) (small : 2 * num < den)
    (sim : Stmt → Fin tapes → Nat → Wit) :
    ¬ MultiTheoremZK (revealSystem verify tapes) sim rel 1 num den budgeted := by
  intro zk
  have asks : ∀ w, rel x w → AsksTrue rel (askOnce x w) := fun w h seen x' w' next => by
    simp only [askOnce] at next
    split at next
    · cases next; exact h
    · cases next
  have g₁ := zk _ admits₁ (asks w₁ h₁)
  have g₂ := zk _ admits₂ (asks w₂ h₂)
  have real : ∀ w, (fun t => (askOnce x w).decide (runReal (revealSystem verify tapes) (askOnce x w) t 1)) =
      fun _ => true := fun w => by
    funext t; simp [runReal, askOnce, revealSystem]
  have simulated : ∀ w, (fun t => (askOnce x w).decide (runSim sim (askOnce x w) t 1)) =
      fun t => (sim x t 0 == w) := fun w => by
    funext t; simp [runSim, askOnce]
  rw [real, simulated] at g₁ g₂
  obtain ⟨positive, _, first, _⟩ := g₁
  obtain ⟨_, _, second, _⟩ := g₂
  have full : (List.ofFn fun (_ : Fin tapes) => true).count true = tapes := by
    rw [List.ofFn_eq_map]; simp
  rw [full] at first second
  have split := count_disjoint (fun t => sim x t 0 == w₁) (fun t => sim x t 0 == w₂)
    (fun t ⟨a, b⟩ => distinct (by simp at a b; exact a.symm.trans b)) (List.finRange tapes)
  rw [← List.ofFn_eq_map, ← List.ofFn_eq_map, List.length_finRange] at split
  have := Nat.mul_le_mul_right den split
  have bound : 2 * (tapes * den) ≤ tapes * den + 2 * (num * tapes) := by nlinarith
  have : tapes * den ≤ tapes * (2 * num) := by nlinarith
  have := Nat.le_of_mul_le_mul_left this positive
  omega

end Teeth

#assert_axioms selectiveOpening_exact
#assert_axioms honest_statement
#assert_axioms Ideal.complete
#assert_axioms Ideal.sound
#assert_axioms Ideal.zk
#assert_axioms reveal_refuted

end Minidregg.Kernel.PrivateCellOpening
