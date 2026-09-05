/-
# Theory.RevocationConsensus -- the negative lifecycle is consensus-bound; the positive one is not

Port of breadstuffs `metatheory/Dregg2/Liveness.lean` (the lifecycle trio at the
verify/find seam), candidate-independent.  `docs/DISTRIBUTED-DESIGN.md` §3.2.

* **Revocation** (kill-while-wanted, the NEGATIVE lifecycle) is consensus-bound.
  `revocation_needs_consensus`: if every party's post-revocation `view` treats
  the cap as gone AND a party only revokes its view after agreeing the epoch
  advanced, then every party agreed (`Consensus`).  Satisfiable at a two-vat
  agreed revocation; teeth at a unilateral one (vat 2 never agreed, so
  `Consensus` fails -- decided).
* **Collection** (collect-when-unwanted, the POSITIVE lifecycle) is not.  The
  ancestor states this in prose beside a `gc_safety_local` that is `id` on a
  definitional synonym.  Here it is a SEPARATION on one decision:
  `collection_needs_no_consensus` -- on the very unilateral decision that fails
  `Consensus`, collection at vat 1 is licensed by vat 1's own release
  (`LocalCollect`); `localCollect_not_consensus` refutes the implication
  `LocalCollect ⇒ Consensus` outright; and `LocalCollect` is two-valued too --
  it fails at vat 2 (`localCollect_teeth`).
* **Deadness is undecidable** (`dead_undecidable`): no computable
  `Code → Bool` decides deadness of the gadget cell across the halting family
  (`haltGraph`), by reduction to `ComputablePred.halting_problem`.  So the
  positive lifecycle is licensed by LOCAL evidence and timed out by lease, never
  decided globally.  The reduction gadget is ported minus the ancestor's `vat`
  colouring, which only its cross-vat-cycle section reads.

Changes from the ancestor: `LivenessGraph` drops `vat`; `LocalCollect` and the
three collection theorems are new (the ancestor's dual was prose); the teeth
are decided, not unfolded by hand.

Residuals: `[LIVENESS-lease]` the ancestor's `Lease`/`leaseExpired`/`Live`
operational completion of `Dead` is not ported; `[LIVENESS-crossvat-cycle]`
`crossvat_cycle_leaks` and `refcount_ne_reachability` are not ported.
-/
import Mathlib.Computability.Halting

namespace Minidregg.Theory.RevocationConsensus

set_option autoImplicit false

/-! ## §1. The negative lifecycle: revocation is consensus-bound. -/

abbrev VatId := ℕ

/-- Revoking a capability while it is still wanted kills authority other vats
may legitimately hold; it is gated by a root epoch every party must agree
advanced.  `agreeing v` records that vat `v` signed off on the advance. -/
structure RevocationDecision where
  epoch : ℕ
  agreeing : VatId → Prop

/-- Every relevant vat agrees the revocation epoch advanced. -/
def Consensus (parties : List VatId) (d : RevocationDecision) : Prop :=
  ∀ v ∈ parties, d.agreeing v

/-- Every relevant party's post-revocation view treats the cap as gone: no
split brain where one vat still honours a cap another revoked.  `view` is
supplied by the operational model. -/
def CrossVatSound (parties : List VatId) (d : RevocationDecision)
    (view : VatId → RevocationDecision → Prop) : Prop :=
  ∀ v ∈ parties, view v d

instance (parties : List VatId) (d : RevocationDecision) [DecidablePred d.agreeing] :
    Decidable (Consensus parties d) :=
  inferInstanceAs (Decidable (∀ v ∈ parties, d.agreeing v))

/-- Cross-vat soundness plus the gate "a vat revokes its view only after
agreeing" forces unanimous agreement. -/
theorem revocation_needs_consensus
    (parties : List VatId) (d : RevocationDecision)
    (view : VatId → RevocationDecision → Prop)
    (hsound : CrossVatSound parties d view)
    (hgate : ∀ v, view v d → d.agreeing v) :
    Consensus parties d :=
  fun v hv => hgate v (hsound v hv)

/-- *Satisfiable*: a two-vat revocation under agreement, with the conclusion
exercised through the theorem. -/
theorem revocation_needs_consensus_satisfiable :
    ∃ (parties : List VatId) (d : RevocationDecision)
      (view : VatId → RevocationDecision → Prop),
      CrossVatSound parties d view
        ∧ (∀ v, view v d → d.agreeing v)
        ∧ Consensus parties d :=
  ⟨[1, 2], ⟨1, fun _ => True⟩, fun _ _ => True,
    fun _ _ => trivial, fun _ _ => trivial,
    revocation_needs_consensus [1, 2] ⟨1, fun _ => True⟩ (fun _ _ => True)
      (fun _ _ => trivial) (fun _ _ => trivial)⟩

/-- *Teeth*: a unilateral revocation -- only vat 1 agreed -- is not a consensus
of `[1, 2]`.  Decided. -/
theorem revocation_needs_consensus_teeth :
    ¬ Consensus [1, 2] (⟨1, fun v => v = 1⟩ : RevocationDecision) := by
  decide

/-! ## §2. The positive lifecycle: collection is local.

A vat collects on its OWN release; no other party's agreement is consulted.
The three statements below are one separation on one decision: the unilateral
decision that fails `Consensus` licenses collection at vat 1. -/

/-- Collection at vat `v` is licensed when `v`, one of the parties, has itself
released.  Only `v`'s own field is read. -/
def LocalCollect (parties : List VatId) (d : RevocationDecision) (v : VatId) : Prop :=
  v ∈ parties ∧ d.agreeing v

instance (parties : List VatId) (d : RevocationDecision) (v : VatId)
    [DecidablePred d.agreeing] : Decidable (LocalCollect parties d v) :=
  inferInstanceAs (Decidable (v ∈ parties ∧ d.agreeing v))

/-- The separation: on the unilateral decision, collection at vat 1 is licensed
while consensus of `[1, 2]` fails.  Both conjuncts decided. -/
theorem collection_needs_no_consensus :
    LocalCollect [1, 2] (⟨1, fun v => v = 1⟩ : RevocationDecision) 1
      ∧ ¬ Consensus [1, 2] (⟨1, fun v => v = 1⟩ : RevocationDecision) := by
  decide

/-- The implication `LocalCollect ⇒ Consensus` is refuted, not merely
unproved: collection never entails agreement of the other party. -/
theorem localCollect_not_consensus :
    ¬ (∀ d : RevocationDecision, LocalCollect [1, 2] d 1 → Consensus [1, 2] d) :=
  fun h => collection_needs_no_consensus.2 (h _ collection_needs_no_consensus.1)

/-- *Teeth* for the local predicate: vat 2 has not released, so collection at
vat 2 is NOT licensed on the same decision. -/
theorem localCollect_teeth :
    ¬ LocalCollect [1, 2] (⟨1, fun v => v = 1⟩ : RevocationDecision) 2 := by
  decide

/-! ## §3. Deadness is undecidable.

`Dead g c` -- `c` unreachable from every root -- is the global predicate the
positive lifecycle would need to decide; it cannot be.  The gadget `haltGraph P`
has one root `0` and one edge `0 → 1` present iff `P`; deciding deadness of `1`
across the halting family would decide halting. -/

abbrev CellId := ℕ

/-- The (possibly cyclic) graph of live references: `edge a b` is an undropped
reference from `a` to `b`; `root` marks holders live by fiat. -/
structure LivenessGraph where
  edge : CellId → CellId → Prop
  root : CellId → Prop

/-- Reflexive-transitive closure of `edge`: a finite path of live references. -/
inductive Reaches (g : LivenessGraph) : CellId → CellId → Prop where
  | refl (a : CellId) : Reaches g a a
  | step {a b c : CellId} : Reaches g a b → g.edge b c → Reaches g a c

/-- Reachable from some root: the finitely-witnessed positive fact. -/
def reachable (g : LivenessGraph) (c : CellId) : Prop :=
  ∃ r : CellId, g.root r ∧ Reaches g r c

/-- Unreachable from every root: the global, non-co-witnessable negative. -/
def Dead (g : LivenessGraph) (c : CellId) : Prop := ¬ reachable g c

/-- The reduction gadget: root `0`, and the single edge `0 → 1` exists iff `P`. -/
def haltGraph (P : Prop) : LivenessGraph where
  edge a b := a = 0 ∧ b = 1 ∧ P
  root a := a = 0

theorem haltGraph_reachable (P : Prop) : reachable (haltGraph P) 1 ↔ P := by
  constructor
  · rintro ⟨r, hr, hpath⟩
    simp only [haltGraph] at hr
    subst hr
    cases hpath with
    | step _ he => exact he.2.2
  · intro hp
    exact ⟨0, rfl, Reaches.step (Reaches.refl 0) ⟨rfl, rfl, hp⟩⟩

theorem haltGraph_dead (P : Prop) : Dead (haltGraph P) 1 ↔ ¬ P := by
  unfold Dead
  rw [haltGraph_reachable]

open Nat.Partrec (Code) in
open Nat.Partrec.Code in
/-- No computable `d : Code → Bool` decides deadness of the gadget cell across
the halting family: it would decide the complement of halting, hence halting. -/
theorem dead_undecidable (n : ℕ) :
    ¬ ∃ d : Code → Bool,
        Computable d ∧
        (∀ c : Code, d c = true ↔ Dead (haltGraph ((eval c n).Dom)) 1) := by
  rintro ⟨d, hcomp, hspec⟩
  have hp : ComputablePred (fun c => d c = true) := by
    apply Computable.computablePred
    simpa using hcomp
  have hp2 : ComputablePred (fun c => ¬ (eval c n).Dom) :=
    hp.of_eq (fun c => by rw [hspec c, haltGraph_dead])
  have hp3 : ComputablePred (fun c => (eval c n).Dom) :=
    hp2.not.of_eq (fun c => by simp)
  exact ComputablePred.halting_problem n hp3

/-! ## §4. Axiom pins. -/

/-- info: 'Minidregg.Theory.RevocationConsensus.revocation_needs_consensus' does not depend on any axioms -/
#guard_msgs in #print axioms revocation_needs_consensus

/-- info: 'Minidregg.Theory.RevocationConsensus.revocation_needs_consensus_satisfiable' does not depend on any axioms -/
#guard_msgs in #print axioms revocation_needs_consensus_satisfiable

/-- info: 'Minidregg.Theory.RevocationConsensus.revocation_needs_consensus_teeth' does not depend on any axioms -/
#guard_msgs in #print axioms revocation_needs_consensus_teeth

/-- info: 'Minidregg.Theory.RevocationConsensus.collection_needs_no_consensus' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms collection_needs_no_consensus

/-- info: 'Minidregg.Theory.RevocationConsensus.localCollect_not_consensus' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms localCollect_not_consensus

/-- info: 'Minidregg.Theory.RevocationConsensus.localCollect_teeth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms localCollect_teeth

/-- info: 'Minidregg.Theory.RevocationConsensus.haltGraph_dead' depends on axioms: [propext] -/
#guard_msgs in #print axioms haltGraph_dead

/-- info: 'Minidregg.Theory.RevocationConsensus.dead_undecidable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dead_undecidable

end Minidregg.Theory.RevocationConsensus
