/-
# Assurance.SemanticReceiptRelation — the clean-sheet receipt as an accumulated relation

This is the first common-relation boundary for the semantic computer. A word
contains pre-state, post-state, and a touched mask. Two quadratic residuals per
key enforce mask Booleanity and the anti-ghost frame law. Their zero set is
proved equivalent to the existence of a `Theory.ReactiveReceipt.ReceiptDelta`.

A valid word is then transported into Selvage's actual `AccClaim`: one shared
evaluation channel binds every coordinate, and `semanticReceiptClaims_fold`
is literally `foldClaims_satisfies`. The folded accumulator word need not be
another literal receipt—exactly as in WARP, it is the linear combination used
by extraction/decision.

This closes the mathematical common relation and fold-closure seam. It does
not claim that a Rust `HistoryEnvelope` implements this word: no Rust semantics
exists in which such a refinement theorem could be stated. Lean emission of
the codec/API and `[PCH-OUTER-ACCUMULATOR]` remain separate boundaries.
-/
import Theory.ReactiveReceipt
import Selvage.Accumulator

namespace Minidregg.Assurance.SemanticReceiptRelation

open Minidregg.Theory.ReactiveReceipt Minidregg.Selvage

variable {Key F : Type*} [Fintype Key] [DecidableEq Key] [Field F] [DecidableEq F]

/-! ## The exact quadratic receipt language -/

/-- The fixed semantic witness carried by one receipt relation. -/
structure ReceiptWitness (Key F : Type*) where
  pre : Store Key F
  post : Store Key F
  touched : Key → F

@[ext] theorem ReceiptWitness.ext {left right : ReceiptWitness Key F}
    (hpre : left.pre = right.pre) (hpost : left.post = right.post)
    (htouched : left.touched = right.touched) : left = right := by
  cases left
  cases right
  cases hpre
  cases hpost
  cases htouched
  rfl

/-- The two individual-degree-two constraints at every key. -/
inductive ConstraintKind
  | boolean
  | frame
  deriving DecidableEq, Fintype

/-- Boolean touched bit, then `(1-touched) * (post-pre)` frame residual. -/
def ReceiptWitness.residual (w : ReceiptWitness Key F) :
    Key × ConstraintKind → F
  | (key, .boolean) => w.touched key * (w.touched key - 1)
  | (key, .frame) => (1 - w.touched key) * (w.post key - w.pre key)

/-- Strict semantic receipt satisfaction. -/
def ReceiptWitness.Satisfies (w : ReceiptWitness Key F) : Prop :=
  ∀ ix, w.residual ix = 0

theorem ReceiptWitness.satisfies_iff (w : ReceiptWitness Key F) :
    w.Satisfies ↔
      (∀ key, w.touched key = 0 ∨ w.touched key = 1) ∧
      (∀ key, (1 - w.touched key) * (w.post key - w.pre key) = 0) := by
  constructor
  · intro h
    refine ⟨fun key => ?_, fun key => h (key, .frame)⟩
    have hz := h (key, .boolean)
    change w.touched key * (w.touched key - 1) = 0 at hz
    rcases mul_eq_zero.mp hz with hzero | hone
    · exact Or.inl hzero
    · exact Or.inr (sub_eq_zero.mp hone)
  · rintro ⟨hbool, hframe⟩ ⟨key, kind⟩
    cases kind with
    | boolean =>
        rcases hbool key with hzero | hone
        · simp [ReceiptWitness.residual, hzero]
        · simp [ReceiptWitness.residual, hone]
    | frame => exact hframe key

/-- Recover the semantic footprint from a satisfying algebraic mask. -/
def ReceiptWitness.touchedFinset (w : ReceiptWitness Key F) : Finset Key :=
  Finset.univ.filter fun key => w.touched key = 1

/-- A satisfying receipt word produces a genuine frame-preserving delta. -/
def ReceiptWitness.toDelta (w : ReceiptWitness Key F) (h : w.Satisfies) :
    ReceiptDelta w.pre w.post where
  touched := w.touchedFinset
  frame := by
    intro key hnot
    have hne : w.touched key ≠ 1 := by
      intro hone
      exact hnot (by simp [ReceiptWitness.touchedFinset, hone])
    have hzero : w.touched key = 0 :=
      (w.satisfies_iff.mp h).1 key |>.resolve_right hne
    have hframe := (w.satisfies_iff.mp h).2 key
    have hsub : w.post key - w.pre key = 0 := by
      simpa [hzero] using hframe
    exact sub_eq_zero.mp hsub

/-- Encode an already-semantic delta back into the quadratic witness. -/
def ReceiptWitness.ofDelta {pre post : Store Key F}
    (delta : ReceiptDelta pre post) : ReceiptWitness Key F where
  pre := pre
  post := post
  touched := fun key => if key ∈ delta.touched then 1 else 0

theorem ReceiptWitness.ofDelta_satisfies {pre post : Store Key F}
    (delta : ReceiptDelta pre post) :
    (ReceiptWitness.ofDelta delta).Satisfies := by
  rw [ReceiptWitness.satisfies_iff]
  constructor
  · intro key
    by_cases h : key ∈ delta.touched <;>
      simp [ReceiptWitness.ofDelta, h]
  · intro key
    by_cases h : key ∈ delta.touched
    · simp [ReceiptWitness.ofDelta, h]
    · simp [ReceiptWitness.ofDelta, h, delta.frame key h]

theorem ReceiptWitness.ofDelta_toDelta (w : ReceiptWitness Key F)
    (h : w.Satisfies) :
    ReceiptWitness.ofDelta (w.toDelta h) = w := by
  apply ReceiptWitness.ext
  · rfl
  · rfl
  · funext key
    rcases (w.satisfies_iff.mp h).1 key with hzero | hone
    · simp [ReceiptWitness.ofDelta, ReceiptWitness.toDelta,
        ReceiptWitness.touchedFinset, hzero, zero_ne_one]
    · simp [ReceiptWitness.ofDelta, ReceiptWitness.toDelta,
        ReceiptWitness.touchedFinset, hone]

/-! ## One canonical fixed-shape word -/

inductive ReceiptSlot
  | pre
  | post
  | touched
  deriving DecidableEq, Fintype

abbrev ReceiptIx (Key : Type*) := Key × ReceiptSlot

/-- Canonical field word: pre, post, touched, with no parallel carrier. -/
def ReceiptWitness.encode (w : ReceiptWitness Key F) : ReceiptIx Key → F
  | (key, .pre) => w.pre key
  | (key, .post) => w.post key
  | (key, .touched) => w.touched key

theorem ReceiptWitness.encode_injective :
    Function.Injective (ReceiptWitness.encode (Key := Key) (F := F)) := by
  intro left right h
  apply ReceiptWitness.ext
  · funext key
    exact congrFun h (key, .pre)
  · funext key
    exact congrFun h (key, .post)
  · funext key
    exact congrFun h (key, .touched)

/-- The common semantic-receipt language consumed by the outer layer. -/
def SemanticReceiptRelation (word : ReceiptIx Key → F) : Prop :=
  ∃ witness : ReceiptWitness Key F,
    witness.Satisfies ∧ word = witness.encode

/-- The algebraic language is exactly the receipt-delta semantics, not merely a
one-way arithmetization. -/
theorem semanticReceiptRelation_iff_delta (word : ReceiptIx Key → F) :
    SemanticReceiptRelation word ↔
      ∃ (pre post : Store Key F) (delta : ReceiptDelta pre post),
        word = (ReceiptWitness.ofDelta delta).encode := by
  constructor
  · rintro ⟨witness, hsat, rfl⟩
    exact ⟨witness.pre, witness.post, witness.toDelta hsat,
      (congrArg ReceiptWitness.encode (witness.ofDelta_toDelta hsat)).symm⟩
  · rintro ⟨pre, post, delta, rfl⟩
    exact ⟨ReceiptWitness.ofDelta delta, ReceiptWitness.ofDelta_satisfies delta, rfl⟩

/-! ## The actual Selvage accumulated claim -/

/-- A receipt admitted to the accumulator carries its semantic validity proof. -/
structure SemanticReceiptClaim (Key F : Type*) [Fintype Key]
    [DecidableEq Key] [Field F] where
  witness : ReceiptWitness Key F
  valid : witness.Satisfies

/-- Coordinate evaluation as a field-linear functional. -/
def evalAt (ix : ReceiptIx Key) : (ReceiptIx Key → F) →ₗ[F] F where
  toFun word := word ix
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def receiptCoord
    (k : Fin (Fintype.card (ReceiptIx Key))) : ReceiptIx Key :=
  (Fintype.equivFin (ReceiptIx Key)).symm k

theorem receiptCoord_surjective (ix : ReceiptIx Key) :
    ∃ k, receiptCoord (Key := Key) k = ix := by
  exact ⟨Fintype.equivFin (ReceiptIx Key) ix, by simp [receiptCoord]⟩

/-- The fixed shared evaluation channel binding every receipt coordinate. -/
noncomputable def SemanticReceiptClaim.acc {Root : Type*}
    (claim : SemanticReceiptClaim Key F) (root : Root) :
    AccClaim Root F (ReceiptIx Key) (Fintype.card (ReceiptIx Key)) :=
  ⟨root, fun k =>
    (evalAt (receiptCoord (Key := Key) k),
      claim.witness.encode (receiptCoord (Key := Key) k))⟩

theorem SemanticReceiptClaim.acc_weights_shared {Root : Type*}
    (left right : SemanticReceiptClaim Key F) (leftRoot rightRoot : Root) :
    ∀ k, (right.acc rightRoot).weights k = (left.acc leftRoot).weights k :=
  fun _ => rfl

/-- Accumulator satisfaction is exactly code membership plus equality to the
canonical valid receipt word. -/
theorem SemanticReceiptClaim.acc_satisfies_iff {Root : Type*}
    {C : Submodule F (ReceiptIx Key → F)}
    (claim : SemanticReceiptClaim Key F) (root : Root)
    (word : ReceiptIx Key → F) :
    AccClaim.Satisfies C (claim.acc root) word ↔
      word ∈ C ∧ word = claim.witness.encode := by
  unfold AccClaim.Satisfies
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    funext ix
    obtain ⟨k, hk⟩ := receiptCoord_surjective (Key := Key) ix
    subst ix
    simpa [SemanticReceiptClaim.acc, AccClaim.weights, AccClaim.targets,
      evalAt] using h k
  · rintro rfl k
    simp [SemanticReceiptClaim.acc, AccClaim.weights, AccClaim.targets, evalAt]

theorem SemanticReceiptClaim.acc_self {Root : Type*}
    {C : Submodule F (ReceiptIx Key → F)}
    (claim : SemanticReceiptClaim Key F) (root : Root)
    (hmem : claim.witness.encode ∈ C) :
    AccClaim.Satisfies C (claim.acc root) claim.witness.encode :=
  (claim.acc_satisfies_iff root _).mpr ⟨hmem, rfl⟩

/-- **The common-relation accumulation join.** Two valid semantic receipts with
words in one linear code fold through Selvage's real WARP-shaped claim. -/
theorem semanticReceiptClaims_fold {Root : Type*}
    {C : Submodule F (ReceiptIx Key → F)}
    (foldRoot : Root → F → Root → Root)
    (left right : SemanticReceiptClaim Key F)
    (leftRoot rightRoot : Root) (gamma : F)
    (hleft : left.witness.encode ∈ C)
    (hright : right.witness.encode ∈ C) :
    AccClaim.Satisfies C
      (foldClaims foldRoot (left.acc leftRoot) (right.acc rightRoot) gamma)
      (left.witness.encode + gamma • right.witness.encode) :=
  foldClaims_satisfies foldRoot gamma
    (left.acc_weights_shared right leftRoot rightRoot)
    (left.acc_self leftRoot hleft) (right.acc_self rightRoot hright)

/-! ## Concrete teeth -/

namespace Example

abbrev ExKey := Fin 2
abbrev ExField := ZMod 5

def pre : Store ExKey ExField := fun _ => 0

def post : Store ExKey ExField
  | 0 => 3
  | 1 => 0

def delta : ReceiptDelta pre post where
  touched := {0}
  frame := by
    intro key h
    fin_cases key <;> simp_all [pre, post]

def good : SemanticReceiptClaim ExKey ExField :=
  ⟨ReceiptWitness.ofDelta delta, ReceiptWitness.ofDelta_satisfies delta⟩

theorem good_relation : SemanticReceiptRelation good.witness.encode :=
  ⟨good.witness, good.valid, rfl⟩

def ghost : ReceiptWitness ExKey ExField where
  pre := pre
  post := post
  touched := fun _ => 0

theorem ghost_rejected : ¬ ghost.Satisfies := by
  intro h
  have hframe := (ghost.satisfies_iff.mp h).2 (0 : ExKey)
  have hthree : (3 : ExField) ≠ 0 := by decide
  apply hthree
  simpa [ghost, pre, post] using hframe

theorem relation_has_teeth : ¬ SemanticReceiptRelation ghost.encode := by
  rintro ⟨witness, hsat, hword⟩
  have hw : witness = ghost := ReceiptWitness.encode_injective hword.symm
  exact ghost_rejected (hw ▸ hsat)

end Example

end Minidregg.Assurance.SemanticReceiptRelation
