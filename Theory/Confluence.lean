/-
# Theory.Confluence — the independence logic: which concurrent inferences commute.

The constitution's third judgement (breadstuffs paper2 §2.4): concurrent turns on a
replicated cell each preserve the cell's invariant locally; do their results MERGE
(the join `⊔` of the cell's state semilattice) invariant-safely? If yes the invariant
is *I-confluent* (Bailis et al., "Coordination avoidance", Thm 3.1) and the cell runs
coordination-free — causal-only, partition-tolerant, no consensus. If no, a concrete
clashing pair exists and the system must ORDER those two turns. The judgement is the
cost label on a guard: not a bug in the guard, the true price of the guard asked for.

Ancestors (ported, redesigned per ATLAS §6):
  * `~/dev/breadstuffs/metatheory/Dregg2/Confluence.lean` — `IConfluent`,
    `admits_sound`, `nonpairwise_escalation`, the `Finset ℕ` poles.
  * `~/dev/breadstuffs/metatheory/Dregg2/Authority/ConfluenceClassifier.lean` —
    the `Guard` language and its monotone / bounded classification.
  The ancestor's `MergeState` wrapper class (a class that only extends
  `SemilatticeSup`) and its `Tier1Eligible` / `guardKeepsConfluence ↔ CoordinationFree`
  synonyms-proved-by-`Iff.rfl` are NOT ported: ATLAS law 1, naming is faking. One name,
  `IConfluent`, over `[SemilatticeSup S]` directly.

What is proved:
  * §1 the judgement and its two directions: `admits_sound` (confluent ⇒ every merge
    lawful) and `nonpairwise_escalation` (not confluent ⇒ a clashing pair exists);
    `iconfluent_iff_join_closed`, the bridge to the subtype of lawful views.
  * §2 the categorical reading, the heart of the N6 poset shadow
    (`docs/KERNEL-NECESSITY.md` §N6): under I-confluence the lawful views form a
    `SemilatticeSup` whose join is the ambient merge (`invariantSemilattice`,
    `coe_sup`), and the merge of two lawful views IS their binary coproduct in the
    lawful subcategory (`merge_is_coproduct`).
  * §3 the sharp edge, as teeth: "binary coproducts exist among the lawful views" does
    NOT imply I-confluence. The five-point lattice `⊥ < a, b < c < ⊤` with the invariant
    `s ≠ c` has ALL binary coproducts on its lawful part (it is the four-point Boolean
    lattice) yet `a ⊔ b = c` is unlawful — the subtype's coproduct of `a, b` sits at
    `⊤`, displaced from the merge (`subtype_lub_does_not_imply_iconfluent`,
    `lawful_join_is_not_the_merge`). This is what forbids the tempting wrong iff.
  * §4 the guard classifier: a monotone floor is always coordination-free
    (`monotone_free`); a ceiling with a clashing split is not (`bounded_breaks`,
    `bounded_forces_ordering` returning the pair). The relational arm's verdict is
    `IConfluent` of its relation by definition — there is no theorem to state.
  * §5 both poles BUILT on two carriers: the grow-only set `Finset ℕ`, and the
    constitution's own example, a two-replica PN-counter `Fin 2 → ℕ × ℕ` under the
    pointwise-max join, where the non-negativity invariant is NOT confluent (two
    concurrent withdrawals of 4 against a balance of 5 merge to −3, values computed)
    while the increments floor on the same carrier IS.

Residual:
  * `[CONFLUENCE-pred-dial]` classifying the one `Pred` AST (`Pred/Core.lean`) under a
    declared per-cell merge is the Pred lane's follow-on; `Guard` here is the
    three-arm shape the classifier lands on, not that AST.
  * `[CONFLUENCE-finality]` consumption of `IConfluent` by the finality tier ladder is
    the `Theory/Finality` lane.
-/
import Mathlib.Order.Lattice
import Mathlib.Order.Bounds.Lattice
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.CategoryTheory.Limits.Preorder
import Mathlib.Tactic.DeriveFintype

namespace Minidregg.Theory.Confluence

open CategoryTheory Limits

universe u

/-! ## §1 — The judgement. -/

/-- A cell invariant: the property admissible turns must preserve. -/
abbrev Invariant (S : Type u) := S → Prop

/-- **I-confluence.** Concurrent invariant-preserving versions merge invariant-safely. -/
def IConfluent {S : Type u} [SemilatticeSup S] (I : Invariant S) : Prop :=
  ∀ x y : S, I x → I y → I (x ⊔ y)

/-- The admission gate: on a confluent cell, every merge of lawful views is lawful. -/
theorem admits_sound {S : Type u} [SemilatticeSup S] {I : Invariant S}
    (h : IConfluent I) {x y : S} (hx : I x) (hy : I y) : I (x ⊔ y) :=
  h x y hx hy

/-- Escalation is forced by a witness: a non-confluent invariant has a concrete
clashing pair — each lawful, their merge not. -/
theorem nonpairwise_escalation {S : Type u} [SemilatticeSup S] {I : Invariant S}
    (hI : ¬ IConfluent I) : ∃ x y : S, I x ∧ I y ∧ ¬ I (x ⊔ y) := by
  by_contra hcon
  exact hI fun x y hx hy => by_contra fun hbad => hcon ⟨x, y, hx, hy, hbad⟩

/-- The bridge to the lawful views: `I` is confluent iff the ambient join of any two
lawful views is lawful. This is the honest iff; §3 shows the categorical strengthening
one might hope for is false. -/
theorem iconfluent_iff_join_closed {S : Type u} [SemilatticeSup S] (I : Invariant S) :
    IConfluent I ↔ ∀ x y : {s // I s}, I (x.1 ⊔ y.1) :=
  ⟨fun h x y => h _ _ x.2 y.2, fun h x y hx hy => h ⟨x, hx⟩ ⟨y, hy⟩⟩

/-! ## §2 — The categorical reading (the N6 poset shadow).

A preorder is a category (`homOfLE`); a join is a binary coproduct
(`Preorder.isColimitBinaryCofan`). Under I-confluence the lawful views inherit the
join, so the merge of two lawful views is their coproduct *inside the lawful
subcategory* — with the coproduct object being the ambient merge, not some other
upper bound. -/

/-- Under `h`, the lawful views form a join-semilattice whose join is the ambient
merge. This is mathlib's `Subtype.semilatticeSup`; its hypothesis is literally
`IConfluent I`. Not an instance — it exists only where `h` does. -/
abbrev invariantSemilattice {S : Type u} [SemilatticeSup S] {I : Invariant S}
    (h : IConfluent I) : SemilatticeSup {s // I s} :=
  Subtype.semilatticeSup h

/-- The subtype join is the ambient join. -/
@[simp] theorem coe_sup {S : Type u} [SemilatticeSup S] {I : Invariant S} (h : IConfluent I)
    (x y : {s // I s}) :
    (letI := invariantSemilattice h; ((x ⊔ y : {s // I s}) : S)) = x.1 ⊔ y.1 :=
  rfl

/-- **The merge is the coproduct.** For lawful views `x y`, the cofan at the ambient
merge `⟨x.1 ⊔ y.1, _⟩` is a colimit in the category of lawful views. -/
theorem merge_is_coproduct {S : Type u} [SemilatticeSup S] {I : Invariant S}
    (h : IConfluent I) (x y : {s // I s}) :
    Nonempty (IsColimit (BinaryCofan.mk (P := (⟨x.1 ⊔ y.1, h _ _ x.2 y.2⟩ : {s // I s}))
      (homOfLE (Subtype.coe_le_coe.mp le_sup_left))
      (homOfLE (Subtype.coe_le_coe.mp le_sup_right)))) :=
  letI := invariantSemilattice h
  ⟨Preorder.isColimitBinaryCofan x y⟩

/-! ## §3 — The sharp edge: coproducts among lawful views do NOT give confluence.

The five-point lattice `⊥ < a, b < c < ⊤` (`a`, `b` incomparable, `a ⊔ b = c`) with the
invariant `s ≠ c`. Its lawful part `{⊥, a, b, ⊤}` is the four-point Boolean lattice —
every pair has a coproduct there — but the coproduct of `a` and `b` is `⊤`, not the
merge `c`. So "the lawful subcategory has binary coproducts" is strictly weaker than
I-confluence; only `iconfluent_iff_join_closed` is the correct iff. -/

/-- The five-point lattice `⊥ < a, b < c < ⊤`. -/
inductive Five
  | bot | a | b | c | top
  deriving DecidableEq, Fintype

namespace Five

/-- The join table: `a ⊔ b = c`, `c` and `⊤` absorb upward, `⊥` is the unit. -/
def sup : Five → Five → Five
  | bot, y => y
  | x, bot => x
  | top, _ => top
  | _, top => top
  | c, _ => c
  | _, c => c
  | a, a => a
  | b, b => b
  | a, b => c
  | b, a => c

instance : LE Five := ⟨fun x y => sup x y = y⟩
instance : DecidableRel (α := Five) (· ≤ ·) :=
  fun x y => inferInstanceAs (Decidable (sup x y = y))

instance : SemilatticeSup Five where
  sup := sup
  le := (· ≤ ·)
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide

/-- The lawful views: everything but `c`. -/
abbrev Lawful := {s : Five // s ≠ c}

/-- The join of the lawful part: as `sup`, except `a ⊔ b = ⊤` (`c` is unlawful). -/
def lawfulSup : Five → Five → Five
  | bot, y => y
  | x, bot => x
  | a, a => a
  | b, b => b
  | _, _ => top

theorem lawfulSup_ne_c : ∀ p q : Five, p ≠ c → q ≠ c → lawfulSup p q ≠ c := by decide
theorem le_lawfulSup_left : ∀ p q : Five, p ≠ c → q ≠ c → p ≤ lawfulSup p q := by decide
theorem le_lawfulSup_right : ∀ p q : Five, p ≠ c → q ≠ c → q ≤ lawfulSup p q := by decide
theorem lawfulSup_le : ∀ p q r : Five,
    p ≠ c → q ≠ c → r ≠ c → p ≤ r → q ≤ r → lawfulSup p q ≤ r := by decide

/-- The lawful part is itself a join-semilattice (the four-point Boolean lattice), under
the order inherited from `Five`. -/
instance : SemilatticeSup Lawful :=
  { Subtype.partialOrder _ with
    sup := fun x y => ⟨lawfulSup x.1 y.1, lawfulSup_ne_c _ _ x.2 y.2⟩
    le_sup_left := fun x y => le_lawfulSup_left _ _ x.2 y.2
    le_sup_right := fun x y => le_lawfulSup_right _ _ x.2 y.2
    sup_le := fun x y z hx hy => lawfulSup_le _ _ _ x.2 y.2 z.2 hx hy }

def aL : Lawful := ⟨a, by decide⟩
def bL : Lawful := ⟨b, by decide⟩
def topL : Lawful := ⟨top, by decide⟩

theorem aL_le_topL : aL ≤ topL := Subtype.coe_le_coe.mp (by decide)
theorem bL_le_topL : bL ≤ topL := Subtype.coe_le_coe.mp (by decide)

/-- `s ≠ c` is not I-confluent: `a`, `b` are lawful and `a ⊔ b = c` is not. -/
theorem avoidC_not_iconfluent : ¬ IConfluent (fun s : Five => s ≠ c) :=
  fun h => h a b (by decide) (by decide) (by decide)

end Five

/-- **The teeth against the wrong iff.** The lawful views of `Five` under `s ≠ c` have
ALL binary coproducts (mathlib's `HasBinaryCoproducts` from the lattice on `Lawful`),
yet the invariant is not I-confluent. -/
theorem subtype_lub_does_not_imply_iconfluent :
    HasBinaryCoproducts Five.Lawful ∧ ¬ IConfluent (fun s : Five => s ≠ Five.c) :=
  ⟨inferInstance, Five.avoidC_not_iconfluent⟩

/-- The displacement, computed: the lawful coproduct of `a`, `b` is `⊤`; their merge is
`c`. The cofan at `⊤` is a colimit among the lawful views. -/
theorem lawful_join_is_not_the_merge :
    ((Five.aL ⊔ Five.bL : Five.Lawful) : Five) = Five.top ∧
      (Five.a ⊔ Five.b : Five) = Five.c ∧
      Nonempty (IsColimit (BinaryCofan.mk (X := Five.aL) (Y := Five.bL) (P := Five.topL)
        (homOfLE Five.aL_le_topL) (homOfLE Five.bL_le_topL))) :=
  ⟨rfl, rfl, ⟨Preorder.isColimitBinaryCofan Five.aL Five.bL⟩⟩

/-! ## §4 — The guard classifier.

Three guard shapes over a merge-state: a grow-only FLOOR (`c ≤ proj s`), a resource
CEILING (`proj s ≤ c`), and an arbitrary RELATIONAL invariant. Each installs an
invariant; `CoordinationFree g` is `IConfluent` of it. -/

/-- An installable guard over a cell whose state merges by `⊔`. -/
inductive Guard (S : Type u)
  /-- A grow-only floor: `proj s ≥ c` (a high-water mark, a sequence number). -/
  | monotone (proj : S → ℕ) (c : ℕ)
  /-- A resource ceiling: `proj s ≤ c` (a budget, a cardinality bound). -/
  | bounded (proj : S → ℕ) (c : ℕ)
  /-- An arbitrary relational invariant; its verdict is decided by the merge. -/
  | relational (I : Invariant S)

/-- The invariant a guard installs. -/
def Guard.inv {S : Type u} : Guard S → Invariant S
  | .monotone proj c => fun s => c ≤ proj s
  | .bounded proj c => fun s => proj s ≤ c
  | .relational I => I

/-- The cost verdict: the guard's cell may run coordination-free. -/
def CoordinationFree {S : Type u} [SemilatticeSup S] (g : Guard S) : Prop :=
  IConfluent g.inv

/-- A floor on a merge-monotone projection is always coordination-free: the merge only
raises the projection. -/
theorem monotone_free {S : Type u} [SemilatticeSup S] {proj : S → ℕ} (hmono : Monotone proj)
    (c : ℕ) : CoordinationFree (.monotone proj c) :=
  fun _ _ hx _ => le_trans hx (hmono le_sup_left)

/-- A ceiling with a clashing split — two states each within the ceiling whose merge
overshoots it — is not coordination-free. -/
theorem bounded_breaks {S : Type u} [SemilatticeSup S] (proj : S → ℕ) (c : ℕ) {x y : S}
    (hx : proj x ≤ c) (hy : proj y ≤ c) (hbad : ¬ proj (x ⊔ y) ≤ c) :
    ¬ CoordinationFree (.bounded proj c) :=
  fun h => hbad (h x y hx hy)

/-- The ceiling's verdict with its witness: not free, and here is the clashing pair. -/
theorem bounded_forces_ordering {S : Type u} [SemilatticeSup S] (proj : S → ℕ) (c : ℕ)
    {x y : S} (hx : proj x ≤ c) (hy : proj y ≤ c) (hbad : ¬ proj (x ⊔ y) ≤ c) :
    ¬ CoordinationFree (.bounded proj c) ∧
      ∃ a b : S, (Guard.bounded proj c).inv a ∧ (Guard.bounded proj c).inv b ∧
        ¬ (Guard.bounded proj c).inv (a ⊔ b) :=
  ⟨bounded_breaks proj c hx hy hbad, x, y, hx, hy, hbad⟩

/-! ## §5 — Both poles, built. -/

namespace Witness

/-! ### The grow-only set `Finset ℕ` (`⊔ = ∪`). -/

/-- The empty invariant is confluent: an unconstrained grow-only set runs free. -/
theorem growOnly_iconfluent : IConfluent (S := Finset ℕ) fun _ => True :=
  fun _ _ _ _ => trivial

/-- A cardinality floor is coordination-free (`Finset.card` is merge-monotone). -/
theorem cardFloor_free (c : ℕ) : CoordinationFree (S := Finset ℕ) (.monotone Finset.card c) :=
  monotone_free Finset.card_mono c

-- The floor fires: two three-element views merge to five elements, still ≥ 3.
example : ({0, 1, 2} ⊔ {2, 3, 4} : Finset ℕ).card = 5 := by decide

/-- A cardinality ceiling is not: `{0}` and `{1}` each have at most one element; their
merge has two. -/
theorem cardLeOne_not_iconfluent : ¬ IConfluent (S := Finset ℕ) fun s => s.card ≤ 1 :=
  bounded_breaks Finset.card 1 (x := {0}) (y := {1}) (by decide) (by decide) (by decide)

/-! ### The constitution's own example: a two-replica PN-counter.

State: per replica, `(increments, decrements)`; merge is pointwise max (each replica's
own counts only grow); balance is `Σ increments − Σ decrements`. -/

/-- Mathlib has `Pi.le_def` but no decidability of `≤` on finite function types at this
pin; this is that instance. Scoped to this namespace: it exists for the witnesses below,
not for every importer's products and functions. -/
scoped instance instDecidableLEPi {ι : Type u} [Fintype ι] {α : ι → Type u} [∀ i, LE (α i)]
    [∀ i, DecidableRel (α := α i) (· ≤ ·)] : DecidableRel (α := ∀ i, α i) (· ≤ ·) :=
  fun s t => decidable_of_iff (∀ i, s i ≤ t i) Iff.rfl

/-- Likewise for the product order (scoped, as above). -/
scoped instance instDecidableLEProd {α β : Type u} [LE α] [LE β] [DecidableRel (α := α) (· ≤ ·)]
    [DecidableRel (α := β) (· ≤ ·)] : DecidableRel (α := α × β) (· ≤ ·) :=
  fun p q => decidable_of_iff (p.1 ≤ q.1 ∧ p.2 ≤ q.2) Iff.rfl

/-- Two replicas, each holding `(increments, decrements)`. -/
abbrev PN := Fin 2 → ℕ × ℕ

/-- The balance read off the counter. -/
def value (s : PN) : ℤ := (∑ i, ((s i).1 : ℤ)) - ∑ i, ((s i).2 : ℤ)

/-- The grow-only projection: total increments. -/
def increments (s : PN) : ℕ := ∑ i, (s i).1

/-- The other grow-only projection: total decrements. -/
def decrements (s : PN) : ℕ := ∑ i, (s i).2

/-- Replica 0 deposited 5 and withdrew 4. -/
def xView : PN := ![(5, 4), (0, 0)]

/-- Concurrently, replica 1 withdrew 4 against the same deposit. -/
def yView : PN := ![(5, 0), (0, 4)]

/-- The numbers: each view has balance 1; their merge has balance −3. -/
theorem pn_overdraft_computed :
    value xView = 1 ∧ value yView = 1 ∧
      xView ⊔ yView = ![(5, 4), (0, 4)] ∧ value (xView ⊔ yView) = -3 := by
  decide

/-- Non-negativity is NOT confluent: two concurrent withdrawals merge to overdraft. -/
theorem nonneg_not_iconfluent : ¬ IConfluent fun s : PN => 0 ≤ value s := fun h =>
  have hbad : 0 ≤ value (xView ⊔ yView) := h xView yView (by decide) (by decide)
  absurd hbad (by decide)

/-- The same failure, classified: it is the ceiling `decrements ≤ 4` breaking on the
split `(4, 0)` / `(0, 4)`. -/
theorem decrements_ceiling_breaks : ¬ CoordinationFree (.bounded decrements 4) :=
  bounded_breaks decrements 4 (x := xView) (y := yView) (by decide) (by decide) (by decide)

theorem increments_mono : Monotone increments :=
  fun _ _ h => Finset.sum_le_sum fun i _ => (h i).1

/-- The other pole on the same carrier: any floor on total increments is
coordination-free — the grow-only reading of the counter. -/
theorem increments_floor_free (c : ℕ) : CoordinationFree (.monotone increments c) :=
  monotone_free increments_mono c

-- The floor fires: both views and their merge carry 5 increments.
example : increments xView = 5 ∧ increments yView = 5 ∧ increments (xView ⊔ yView) = 5 := by
  decide

end Witness

/-! ## §6 — Axiom pins. -/

/-- info: 'Minidregg.Theory.Confluence.admits_sound' does not depend on any axioms -/
#guard_msgs in #print axioms admits_sound

/-- info: 'Minidregg.Theory.Confluence.nonpairwise_escalation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nonpairwise_escalation

/-- info: 'Minidregg.Theory.Confluence.iconfluent_iff_join_closed' does not depend on any axioms -/
#guard_msgs in #print axioms iconfluent_iff_join_closed

/-- info: 'Minidregg.Theory.Confluence.merge_is_coproduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms merge_is_coproduct

/--
info: 'Minidregg.Theory.Confluence.subtype_lub_does_not_imply_iconfluent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms subtype_lub_does_not_imply_iconfluent

/-- info: 'Minidregg.Theory.Confluence.lawful_join_is_not_the_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lawful_join_is_not_the_merge

/-- info: 'Minidregg.Theory.Confluence.monotone_free' does not depend on any axioms -/
#guard_msgs in #print axioms monotone_free

/-- info: 'Minidregg.Theory.Confluence.bounded_breaks' does not depend on any axioms -/
#guard_msgs in #print axioms bounded_breaks

/-- info: 'Minidregg.Theory.Confluence.bounded_forces_ordering' does not depend on any axioms -/
#guard_msgs in #print axioms bounded_forces_ordering

/-- info: 'Minidregg.Theory.Confluence.Witness.cardFloor_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Witness.cardFloor_free

/--
info: 'Minidregg.Theory.Confluence.Witness.cardLeOne_not_iconfluent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Witness.cardLeOne_not_iconfluent

/-- info: 'Minidregg.Theory.Confluence.Witness.pn_overdraft_computed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Witness.pn_overdraft_computed

/-- info: 'Minidregg.Theory.Confluence.Witness.nonneg_not_iconfluent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Witness.nonneg_not_iconfluent

/--
info: 'Minidregg.Theory.Confluence.Witness.decrements_ceiling_breaks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Witness.decrements_ceiling_breaks

/-- info: 'Minidregg.Theory.Confluence.Witness.increments_floor_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Witness.increments_floor_free

end Minidregg.Theory.Confluence
