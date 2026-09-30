/-
# Kernel.TurnRecord -- accepted effects as legs, and the physical refinement over `step`

Two bridges from the pre-B2 durable model to `Kernel.World`:

* **An accepted effect is a leg.**  `AcceptedCellEffect` already carries the
  family patch validated at the canonical pre-store.  `Leg.ofAccepted` puts
  that patch, unchanged, into a turn.  `step` then installs
  `run pre.logical (family.patch d o)` at the cell, so the post root a
  `DurableCommitProtocol.RootWrite.exactPost` used to carry is *derived* from
  the world (`step_ofAccepted_root`), and a world holding the pre-store never
  refuses the leg (`applyLeg_ofAccepted`).
* **Physical atomicity is a simulation of `step`.**
  `ImplementationRefinement` is `DurableCommitProtocol.ImplementationRefinement`
  re-indexed by `Turn` and `World`: every physical step represents either the
  old world or the world `step` produced (`physical_step_exact`).  Crash
  schedules become the trace theorem `trace_represents_fold`: a physical trace
  over a log always represents the fold of a sublist of that log from genesis.
  The torn install (cells without the system half) refutes the premise
  (`Example.torn_not_refinement`).
-/
import Kernel.World
import Theory.AcceptedCellEffect

namespace Minidregg.Kernel.TurnRecord

open Minidregg.Theory
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.World

set_option autoImplicit false

universe z q

/-! ## An accepted effect is a leg -/

section Accepted

variable {R : Registry} {k : R.Kind}
    {M : CellState.Materializer (R.layout k) Digest} {Nullifier : Type}
    {family : SemanticEffectFamily.{0, 0, 0, 0, z} (R.layout k) M Nullifier}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {request : Request kind} {pre : CellState.Materialized M}
    {declaration : family.Declaration} {outcome : family.Outcome declaration}

/-- The leg of an accepted effect at cell `c`: the family patch, unchanged. -/
def Leg.ofAccepted (c : CellId)
    (_accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) : Leg R :=
  ⟨c, k, family.patch declaration outcome⟩

/-- A cell map holding the accepted effect's pre-store at its kind admits the
leg, and installs exactly the validated post. -/
theorem applyLeg_ofAccepted (cells : Cells R) (c : CellId)
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome)
    (holds : cells c = some ⟨k, pre.logical⟩) :
    applyLeg cells (Leg.ofAccepted c accepted) =
      .ok (cells.update c (some ⟨k, accepted.validated.apply.logical⟩)) := by
  have hfd : Patch.firstDisabled? pre.logical (family.patch declaration outcome) = none :=
    (Patch.firstDisabled?_eq_none_iff _ _).2 accepted.validated.valid
  unfold applyLeg
  simp only [Leg.ofAccepted, holds, Cell.storeAt_self, hfd]
  rfl

/-- **`exactPost` is derived.**  When `step` accepts a turn carrying the
accepted effect's leg at a cell that held its pre-store, the cell's post store
is the validated post and its materialized root is
`M.rootOf (run pre.logical (family.patch d o))`: the value the deleted
`DurableCommitProtocol.Intent.ofAcceptedEffect_rootWrites` equated with the
`RootWrite.exactPost` its intent carried, now read off the world. -/
theorem step_ofAccepted_root {TxId Ev D : Type} [DecidableEq TxId] [DecidableEq D]
    (H : History R TxId Ev D) {w w' : World R TxId D} {t : Turn R TxId Ev}
    (h : World.step H w t = some w') (c : CellId)
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome)
    (m : Leg.ofAccepted c accepted ∈ t.legs)
    (hc : c ∉ t.creates.map Prod.fst) (hr : c ∉ t.retires)
    (holds : w.cells c = some ⟨k, pre.logical⟩) :
    w'.cells c = some ⟨k, accepted.validated.apply.logical⟩ ∧
      ((w'.cells c).bind (·.storeAt k)).map M.rootOf =
        some (M.rootOf (Patch.run pre.logical (family.patch declaration outcome))) := by
  obtain ⟨pre', hpre, _, hpost⟩ := step_leg H h (Leg.ofAccepted c accepted) m hc hr
  simp only [Leg.ofAccepted, holds, Option.bind_some, Cell.storeAt_self,
    Option.some.injEq] at hpre
  subst hpre
  refine ⟨hpost, ?_⟩
  simp only [Leg.ofAccepted] at hpost
  rw [hpost]
  simp

/-- Satisfiable pole at the seam: a one-leg turn carrying an accepted effect,
at a fresh id and a present head, is accepted by `step`, and installs the
validated post. -/
theorem step_single_accepted {TxId Ev D : Type} [DecidableEq TxId] [DecidableEq D]
    (H : History R TxId Ev D) (w : World R TxId D) (c : CellId) (x : TxId) (ev : Ev)
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome)
    (holds : w.cells c = some ⟨k, pre.logical⟩)
    {height : Nat} {logRoot : D} (hh : w.head = some (height, logRoot))
    (fresh : w.journal x = none) :
    ∃ w', World.step H w ⟨x, [], [Leg.ofAccepted c accepted], [], ev⟩ = some w' ∧
      w'.cells c = some ⟨k, accepted.validated.apply.logical⟩ := by
  let t : Turn R TxId Ev := ⟨x, [], [Leg.ofAccepted c accepted], [], ev⟩
  have hcells : applyCells w.cells t =
      .ok (w.cells.update c (some ⟨k, accepted.validated.apply.logical⟩)) := by
    unfold applyCells
    simp only [t, applyCreates, applyLegs, applyLeg_ofAccepted w.cells c accepted holds,
      applyRetires]
  have shaped : Shaped t := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [t]
  have hv := sysPatch_valid_plain H (t := t) rfl rfl fresh hh
  refine ⟨_, (step_eq_some H).2 (admit_of H shaped hh fresh hv hcells), ?_⟩
  exact cells_update_self _ _ _

end Accepted

/-! ## Physical implementation refinement, re-indexed by `Turn` and `World` -/

section Refinement

variable {R : Registry} {TxId Ev D : Type} [DecidableEq TxId] [DecidableEq D]
variable (H : History R TxId Ev D)

/-- A physical handler refines the fold only by a simulation indexed by its
actual states and steps: each physical step represents either the old world
(nothing took: a refusal, or a crash before the atomic install) or exactly
the world `step` produced (a completed install, possibly with a lost
reply).  `PhysicalStep` is proof-relevant evidence, not a Boolean. -/
structure ImplementationRefinement (PhysicalState : Type)
    (PhysicalStep : PhysicalState → Turn R TxId Ev → PhysicalState → Type q)
    (Represents : PhysicalState → World R TxId D → Prop) : Prop where
  simulates : ∀ {pb pa : PhysicalState} {wb : World R TxId D} {t : Turn R TxId Ev},
    Represents pb wb → PhysicalStep pb t pa →
      Represents pa wb ∨ ∃ wa, World.step H wb t = some wa ∧ Represents pa wa

/-- **No partial commit.**  A refining physical step represents the complete
old world or the complete stepped world; there is no third state. -/
theorem physical_step_exact {PhysicalState : Type}
    {PhysicalStep : PhysicalState → Turn R TxId Ev → PhysicalState → Type q}
    {Represents : PhysicalState → World R TxId D → Prop}
    (refinement : ImplementationRefinement H PhysicalState PhysicalStep Represents)
    {pb pa : PhysicalState} {wb : World R TxId D} {t : Turn R TxId Ev}
    (represented : Represents pb wb) (stepped : PhysicalStep pb t pa) :
    ∃ wa, Represents pa wa ∧ (wa = wb ∨ World.step H wb t = some wa) := by
  rcases refinement.simulates represented stepped with keep | ⟨wa, hs, hr⟩
  · exact ⟨wb, keep, .inl rfl⟩
  · exact ⟨wa, hr, .inr hs⟩

/-- A physical trace: physical steps, one per submitted turn. -/
inductive Trace {PhysicalState : Type}
    (PhysicalStep : PhysicalState → Turn R TxId Ev → PhysicalState → Type q) :
    PhysicalState → List (Turn R TxId Ev) → PhysicalState → Type (max q 1)
  | nil (p : PhysicalState) : Trace PhysicalStep p [] p
  | snoc {p p' p'' : PhysicalState} {log : List (Turn R TxId Ev)} {t : Turn R TxId Ev} :
      Trace PhysicalStep p log p' → PhysicalStep p' t p'' → Trace PhysicalStep p (log ++ [t]) p''

/-- **Crash recovery as a fold.**  Whatever crashes and refusals a refining
handler went through, its state represents the fold, from the genesis it
started at, of a sublist of the submitted turns: every turn either took
completely, in order, or not at all. -/
theorem trace_represents_fold {PhysicalState : Type}
    {PhysicalStep : PhysicalState → Turn R TxId Ev → PhysicalState → Type q}
    {Represents : PhysicalState → World R TxId D → Prop}
    (refinement : ImplementationRefinement H PhysicalState PhysicalStep Represents)
    {p0 p : PhysicalState} {g : World R TxId D} {log : List (Turn R TxId Ev)}
    (start : Represents p0 g) (trace : Trace PhysicalStep p0 log p) :
    ∃ sub W, sub.Sublist log ∧ fold H g sub = some W ∧ Represents p W := by
  induction trace with
  | nil => exact ⟨[], g, List.Sublist.slnil, rfl, start⟩
  | snoc _ step ih =>
      obtain ⟨sub, W, hsub, hfold, hrep⟩ := ih
      rcases refinement.simulates hrep step with keep | ⟨W', hs, hr⟩
      · exact ⟨sub, W, hsub.trans (List.sublist_append_left _ _), hfold, keep⟩
      · refine ⟨sub ++ [_], W', hsub.append (List.Sublist.refl _), ?_, hr⟩
        rw [fold_snoc, hfold]
        exact hs

end Refinement

/-! ## Poles -/

namespace Example

open Minidregg.Kernel.World.Example

/-- The model itself as a handler: a physical step is `step`, or a refusal
that keeps the state. -/
def modelStep (p : ToyWorld) (t : ToyTurn) (p' : ToyWorld) : Type :=
  PLift (World.step toyH p t = some p' ∨ (World.step toyH p t = none ∧ p' = p))

/-- Satisfiable pole: the model refines itself. -/
theorem model_refinement : ImplementationRefinement toyH ToyWorld modelStep Eq := by
  refine ⟨fun {pb pa wb t} rep st => ?_⟩
  subst rep
  rcases st.down with hs | ⟨_, rfl⟩
  · exact .inr ⟨pa, hs, rfl⟩
  · exact .inl rfl

/-- The torn install: the turn's cell half without its system half. -/
def tornStep (p : ToyWorld) (t : ToyTurn) (p' : ToyWorld) : Type :=
  PLift (∃ cells, applyCells p.cells t = .ok cells ∧ p' = { p with cells := cells })

def tornPost : ToyWorld :=
  { w1 with cells := match applyCells w1.cells t1 with | .ok c => c | .error _ => w1.cells }

theorem torn_cells_ok : (applyCells w1.cells t1).toBool = true := by decide +kernel

def tornPost_step : tornStep w1 t1 tornPost := ⟨by
  have ok := torn_cells_ok
  unfold tornPost
  cases h : applyCells w1.cells t1 with
  | error e => rw [h] at ok; cases ok
  | ok c => exact ⟨c, rfl, rfl⟩⟩

/-- The torn world moved a cell (so it is not the old world) and wrote no
journal entry (so it is not the stepped world). -/
theorem torn_distinguished :
    val tornPost 0 ≠ val w1 0 ∧
      ((World.step toyH w1 t1).map fun w => w.journal 2) ≠ some (tornPost.journal 2) := by
  decide +kernel

/-- Refuting pole: the torn handler does not refine the fold. -/
theorem torn_not_refinement : ¬ ImplementationRefinement toyH ToyWorld tornStep Eq := by
  intro refinement
  rcases refinement.simulates rfl tornPost_step with keep | ⟨wa, hs, hr⟩
  · exact torn_distinguished.1 (by rw [keep])
  · apply torn_distinguished.2
    rw [hs, hr]
    rfl

end Example


/-! ## Axiom pins -/

/-- info: 'Minidregg.Kernel.TurnRecord.applyLeg_ofAccepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms applyLeg_ofAccepted
/-- info: 'Minidregg.Kernel.TurnRecord.step_ofAccepted_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_ofAccepted_root
/-- info: 'Minidregg.Kernel.TurnRecord.step_single_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_single_accepted
/-- info: 'Minidregg.Kernel.TurnRecord.physical_step_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms physical_step_exact
/-- info: 'Minidregg.Kernel.TurnRecord.trace_represents_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms trace_represents_fold
/-- info: 'Minidregg.Kernel.TurnRecord.Example.model_refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.model_refinement
/-- info: 'Minidregg.Kernel.TurnRecord.Example.torn_cells_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.torn_cells_ok
/-- info: 'Minidregg.Kernel.TurnRecord.Example.torn_distinguished' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.torn_distinguished
/-- info: 'Minidregg.Kernel.TurnRecord.Example.torn_not_refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.torn_not_refinement

end Minidregg.Kernel.TurnRecord
