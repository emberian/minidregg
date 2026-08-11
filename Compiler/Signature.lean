/-
# Compiler.Signature — N3 "one induction": initiality as LAW, over an abstract signature

## What this file is (KERNEL-NECESSITY §N3)

Breadstuffs proved initiality for ONE concrete IR (`Metatheory/Dynamics/Initiality.lean`:
a `StmtAlgebra` with one field per `RecStmt` constructor, `foldStmt`, `IsFoldHom`,
`fold_unique`, `agree_by_initiality`) — and then paid for the missing law with
`compile_not_a_seq_hom`: the circuit reading was NOT a fold, so the N²→1 agreement
collapse was PARTIAL, and three compiles + 11K lines of welds followed. That file is
the SHAPE. This file is the LAW: the same development over an ABSTRACT polynomial
signature — shapes + per-shape arity, nothing else — so every IR this repo grows gets
`fold_unique` by INSTANTIATION (one `Alg` value per reading), never by re-proof.
The one induction lives here, once (`fold_unique`, §4).

## Mathlib reuse (audited at pin 1c2b90b / v4.30.0)

* `PFunctor` (`Mathlib.Data.PFunctor.Univariate.Basic`) IS this container shape.
  `Signature` keeps kernel-facing field names (`Op`/`ar` — the effect vocabulary),
  with `signatureEquivPFunctor` the definitional isomorphism; nothing is re-derived.
* `WType S.ar` (`Mathlib.Data.W.Basic`) IS the free term algebra — `Term` is an
  `abbrev` for it, not a re-declared inductive; `Term S = S.toPFunctor.W` by `rfl`
  (`term_eq_pfunctor_W`).
* `WType.elim` IS the fold — `fold` is its curried form (`fold_eq_elim : rfl`).
* What mathlib does NOT have at this pin: UNIQUENESS of `elim` (it ships only
  `elim_injective`). `fold_unique`, `agree_by_initiality`, `fold_termAlg` (the
  Lambek-flavored "the identity is the unique endo-fold"), and the N3-converse
  obligation are the content authored here.

## Boundary

Imports Mathlib only (Compiler may import Mathlib + Theory + Compiler).
-/
import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Data.Countable.Defs

namespace Minidregg.Compiler

universe u v w

/-! ## §1. `Signature` — shapes + per-shape arity (the container, kernel-named).

A signature is exactly the data of a polynomial functor: a type of operation SHAPES
and, for each shape, an ARITY type indexing its recursive slots. Leaves are shapes
with empty arity; parameter payloads live inside `Op` (a shape per payload value).
This is mathlib's `PFunctor` under the names the kernel speaks (`Op`/`ar`); the
isomorphism is definitional and recorded (`signatureEquivPFunctor`), and all term
machinery below routes through mathlib's `WType`. -/

/-- **`Signature`** — an abstract polynomial signature: a type `Op` of operation
shapes and a family `ar` assigning each shape its arity (the type indexing its
recursive argument slots). Container style: this is `PFunctor` with kernel-facing
field names. A LEAF is a shape `s` with `ar s` empty; an `n`-ary node is a shape
with `ar s ≃ Fin n`; infinitary nodes are legal (arbitrary `ar s`). -/
structure Signature where
  /-- Operation shapes (one per constructor-with-parameters of the intended IR). -/
  Op : Type u
  /-- Per-shape arity: the type indexing the recursive slots of shape `s`. -/
  ar : Op → Type v

/-- The polynomial functor of a signature — mathlib's `PFunctor`, reused verbatim. -/
def Signature.toPFunctor (S : Signature.{u, v}) : PFunctor.{u, v} :=
  ⟨S.Op, S.ar⟩

/-- `Signature` IS `PFunctor` up to field names — the definitional isomorphism,
recorded so no reviewer has to take "container style" on faith. -/
def signatureEquivPFunctor : Signature.{u, v} ≃ PFunctor.{u, v} where
  toFun S := ⟨S.Op, S.ar⟩
  invFun P := ⟨P.A, P.B⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## §2. The free term algebra — mathlib's W-type, reused, not re-derived. -/

/-- **`Term S`** — the free term algebra over `S`: well-founded trees with nodes
labeled by shapes and children indexed by arities. This is mathlib's `WType S.ar`
by `abbrev` (not a parallel inductive): the initial `S`-algebra. -/
abbrev Term (S : Signature.{u, v}) : Type max u v :=
  WType S.ar

/-- `Term S` is definitionally `S.toPFunctor.W` — the reuse is on the nose. -/
theorem term_eq_pfunctor_W (S : Signature.{u, v}) : Term S = S.toPFunctor.W :=
  rfl

/-! ## §3. Algebras and the fold.

An `S`-algebra on carrier `α` chooses one operation per shape, consuming the carrier
values of the recursive slots — the curried form of a `PFunctor`-algebra structure
map `S.toPFunctor α → α` (`algEquivStructureMap`). The fold is the catamorphism;
it IS mathlib's `WType.elim` (`fold_eq_elim`), packaged for the curried shape. -/

/-- **`Alg S α`** — an `S`-algebra structure on `α`: one operation per shape,
taking the carrier values at that shape's arity. Choosing an `Alg` is choosing how
to READ each primitive; the fold (below) is the unique extension to whole terms. -/
abbrev Alg (S : Signature.{u, v}) (α : Type w) : Type max u v w :=
  (s : S.Op) → (S.ar s → α) → α

/-- `Alg S α` is the curried form of a `PFunctor`-algebra structure map — the
mathlib-facing `F`-algebra presentation, definitionally. -/
def algEquivStructureMap (S : Signature.{u, v}) (α : Type w) :
    Alg S α ≃ (S.toPFunctor.Obj α → α) where
  toFun alg x := alg x.1 x.2
  invFun m s k := m ⟨s, k⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **`fold alg`** — the catamorphism induced by an `S`-algebra: the unique
`S`-algebra homomorphism `Term S → α` (uniqueness is `fold_unique`). Defined AS
mathlib's `WType.elim` (curried), not re-derived. -/
def fold {S : Signature.{u, v}} {α : Type w} (alg : Alg S α) : Term S → α :=
  WType.elim α fun x => alg x.1 x.2

/-- `fold` is `WType.elim` on the nose — the reuse, recorded. -/
theorem fold_eq_elim {S : Signature.{u, v}} {α : Type w} (alg : Alg S α) :
    fold alg = WType.elim α (algEquivStructureMap S α alg) :=
  rfl

/-- The computation rule: `fold` applies the algebra at the root to the folded
children — definitionally. -/
@[simp]
theorem fold_mk {S : Signature.{u, v}} {α : Type w} (alg : Alg S α)
    (s : S.Op) (k : S.ar s → Term S) :
    fold alg (.mk s k) = alg s fun i => fold alg (k i) :=
  rfl

/-! ## §4. `IsFoldHom` and `fold_unique` — THE one induction.

`IsFoldHom alg f` is the universal-property hom-condition: `f` agrees with the
algebra at every node, compositionally on the recursive values. `fold_unique` is
the uniqueness half of initiality — proved by the ONE structural induction of this
development; every downstream agreement result invokes it with zero further
induction. -/

/-- **`IsFoldHom alg f`** — `f : Term S → α` is an `S`-algebra homomorphism for
`alg`: at every node it equals the algebra's operation applied to its own values on
the children. (In breadstuffs' concrete precedent this was one structure field per
constructor; over an abstract signature it is one `∀` over shapes.) -/
def IsFoldHom {S : Signature.{u, v}} {α : Type w} (alg : Alg S α)
    (f : Term S → α) : Prop :=
  ∀ (s : S.Op) (k : S.ar s → Term S), f (.mk s k) = alg s fun i => f (k i)

/-- The canonical fold is a homomorphism — the existence half of initiality. -/
theorem fold_isFoldHom {S : Signature.{u, v}} {α : Type w} (alg : Alg S α) :
    IsFoldHom alg (fold alg) :=
  fun _ _ => rfl

/-- `IsFoldHom` is the genuine `F`-algebra homomorphism square
`f ∘ mk = alg ∘ F f`, phrased through mathlib's `PFunctor.map` — the categorical
hom-condition, definitionally equivalent to the per-node form. -/
theorem isFoldHom_iff_algebra_square {S : Signature.{u, v}} {α : Type w}
    (alg : Alg S α) (f : Term S → α) :
    IsFoldHom alg f ↔
      ∀ x : S.toPFunctor.Obj (Term S),
        f (PFunctor.W.mk x) = algEquivStructureMap S α alg (S.toPFunctor.map f x) := by
  constructor
  · rintro h ⟨s, k⟩
    exact h s k
  · intro h s k
    exact h ⟨s, k⟩

/-- **`fold_unique` — UNIQUENESS OF THE FOLD (initiality of `Term S`).** Any
`S`-algebra homomorphism for `alg` equals the canonical fold, on every term. THE
one induction of the N3 program: every reading-agreement in the tree is a corollary
of this theorem at some `Alg`, with no further induction anywhere. -/
theorem fold_unique {S : Signature.{u, v}} {α : Type w} (alg : Alg S α)
    (f : Term S → α) (hf : IsFoldHom alg f) : f = fold alg := by
  funext t
  induction t with
  | mk s k ih =>
    rw [hf s k, fold_mk]
    exact congrArg (alg s) (funext ih)

/-! ## §5. `agree_by_initiality` — the N²→1 collapse, generic form.

Two readings that are both homomorphisms of the SAME algebra agree on every term —
by `fold_unique` twice, with no induction at the use site. This is the payoff N3
names as law: executor⟺circuit⟺cost-model⟺explainer agreement is one theorem per
PAIRING OF READINGS WITH ONE ALGEBRA, not one induction per pair. -/

/-- **`agree_by_initiality` — two fold-homomorphisms of one algebra agree on every
term.** The generic N²→1 collapse: agreement of any two readings is free the moment
both are folds of the same algebra. No induction at the use site. -/
theorem agree_by_initiality {S : Signature.{u, v}} {α : Type w} (alg : Alg S α)
    (f g : Term S → α) (hf : IsFoldHom alg f) (hg : IsFoldHom alg g) : f = g := by
  rw [fold_unique alg f hf, fold_unique alg g hg]

/-- Pointwise form — the shape a caller consuming "the two readings agree on THIS
term" uses. -/
theorem agree_by_initiality_pointwise {S : Signature.{u, v}} {α : Type w}
    (alg : Alg S α) (f g : Term S → α) (hf : IsFoldHom alg f) (hg : IsFoldHom alg g)
    (t : Term S) : f t = g t :=
  congrFun (agree_by_initiality alg f g hf hg) t

/-- The term-constructor algebra: `Term S` is an `S`-algebra over itself. -/
def termAlg (S : Signature.{u, v}) : Alg S (Term S) :=
  fun s k => .mk s k

/-- Lambek-flavored corollary: the fold of the term-constructor algebra is the
identity — no fold can rebuild terms differently than they were built. (The
identity is a hom by `rfl`; uniqueness does the rest.) -/
theorem fold_termAlg (S : Signature.{u, v}) : fold (termAlg S) = id :=
  (fold_unique (termAlg S) id fun _ _ => rfl).symm

/-! ## §6. NON-VACUITY — a two-op signature, two genuinely different algebras,
the collapse EXERCISED.

A uniqueness theorem that never forces anything is decoration. We instantiate the
whole §1–§5 apparatus at the smallest interesting signature — one nullary leaf, one
binary node — with two algebras that genuinely disagree (`demo_folds_differ`), an
independently hand-recursed reading proved equal to the fold BY the collapse with
zero induction at the use site (`demo_collapse_exercised`), and the value of a
compound two-level term pinned for EVERY homomorphism (`demo_collapse_pins_compound`). -/

/-- Demo shapes: a nullary leaf and a binary node. -/
inductive DemoOp : Type
  | leaf
  | node

/-- The demo signature: `leaf` has empty arity, `node` has `Bool`-indexed (binary)
arity. -/
def DemoSig : Signature where
  Op := DemoOp
  ar := fun s => match s with
    | .leaf => Empty
    | .node => Bool

/-- The leaf term. -/
def lf : Term DemoSig :=
  .mk .leaf nofun

/-- A binary node term (`false` slot = left, `true` slot = right). -/
def nd (l r : Term DemoSig) : Term DemoSig :=
  .mk .node fun b => bif b then r else l

/-- Reading 1: count leaves (`leaf ↦ 1`, `node ↦ +`). -/
def sizeAlg : Alg DemoSig ℕ := fun s => match s with
  | .leaf => fun _ => 1
  | .node => fun k => k false + k true

/-- Reading 2: tree depth (`leaf ↦ 0`, `node ↦ max + 1`) — same carrier, genuinely
different algebra. -/
def depthAlg : Alg DemoSig ℕ := fun s => match s with
  | .leaf => fun _ => 0
  | .node => fun k => max (k false) (k true) + 1

/-- A compound two-level term: `nd lf (nd lf lf)`. -/
def demoTree : Term DemoSig :=
  nd lf (nd lf lf)

/-- The two folds compute (leaf count 3, depth 2). -/
theorem demo_values : fold sizeAlg demoTree = 3 ∧ fold depthAlg demoTree = 2 := by
  constructor <;> rfl

/-- **Two genuinely different algebras have genuinely different folds** — the
collapse below is about two readings of ONE algebra, not a claim that all readings
agree; witnessed on the compound term (3 ≠ 2). -/
theorem demo_folds_differ : fold sizeAlg ≠ fold depthAlg := fun h =>
  absurd (congrFun h demoTree) (by decide)

/-- An INDEPENDENT hand-recursed reading of the size algebra — written by direct
structural recursion, not via `fold` (the "executor" of the demo). -/
def leafCount : Term DemoSig → ℕ
  | .mk .leaf _ => 1
  | .mk .node k => leafCount (k false) + leafCount (k true)

/-- The hand-recursed reading is a fold-homomorphism of `sizeAlg` — one `rfl` per
shape, NO induction. -/
theorem leafCount_isFoldHom : IsFoldHom sizeAlg leafCount := by
  intro s k
  cases s with
  | leaf => rfl
  | node => rfl

/-- **The collapse, EXERCISED**: the hand-recursed reading equals the derived fold
on EVERY term, by `agree_by_initiality` — zero induction at the use site (the one
induction was spent in `fold_unique`, once, generically). -/
theorem demo_collapse_exercised : leafCount = fold sizeAlg :=
  agree_by_initiality sizeAlg leafCount (fold sizeAlg)
    leafCount_isFoldHom (fold_isFoldHom sizeAlg)

/-- The collapse BITES on a compound term: ANY homomorphism of `sizeAlg` is forced
to the value 3 on the two-level `demoTree` — per-shape agreement pins non-atomic
terms, the genuine content of initiality. -/
theorem demo_collapse_pins_compound (f : Term DemoSig → ℕ)
    (hf : IsFoldHom sizeAlg f) : f demoTree = 3 := by
  rw [fold_unique sizeAlg f hf]
  rfl

/-! ## §7. The N3 CONVERSE — opaque payloads forbid a faithful second reading.

### The law being stated ("syntactic leaves are forced")

§1–§5 give the positive direction of N3: POLYNOMIAL signature ⟹ every reading
that is a fold agrees with every other by initiality, one induction total. The
converse obligation is the negative direction KERNEL-NECESSITY §N3 asks for:
if constructor payloads are OPAQUE SEMANTIC OBJECTS (functions, not syntax), then
interpretations exist but no COMPOSITIONAL SECOND READING into syntax can be
faithful to them — so "everything derived" (derivation-totality) FORCES syntactic
leaves. Breadstuffs paid for this negatively: `RecStmt.guard` carried a closure
`RecordKernelState → Bool`, `compile` had nothing syntactic to recurse into, and
`compile_not_a_seq_hom` proved the shipped circuit reading was not a fold. The
law says: with opaque leaves it could never have been a FAITHFUL one.

### Formalization choices (flagged, honestly)

1. **"Non-polynomial" is not a negatable property of a `Signature` value** — every
   `Signature` is a container by construction. Opacity is a property of what `Op`
   is BUILT FROM: a full function space `σ → Bool` (semantic payloads, cardinality
   `2^ℵ₀`) versus countable syntax (`Pred` codes). We therefore state the law at
   the CANONICAL minimal witness `OpaqueSig ℕ` — one opaque guard-leaf family plus
   one binary sequencing node, exactly breadstuffs' `guard`/`seq` fragment. Any IR
   whose `Op` embeds this family inherits the obstruction by precomposing its fold
   with the embedding of terms.
2. **"Syntactic target" is formalized as `Countable`** — descriptors, circuits,
   cost tables, explainer strings are finite objects over countable alphabets,
   hence countable. Countability is the WEAKEST such rendering, which makes the
   obligation the STRONGEST honest claim (no computability assumption smuggled in;
   the collapse is already cardinality-forced).
3. **Two faces.** `OpaqueConflation`: every fold into a countable target CONFLATES
   two guard leaves that the executor (`opaqueRun`, a genuine fold, so folds DO
   exist — the obstruction is faithfulness, not existence) SEPARATES.
   `NoFaithfulSyntacticReading`: no decoding of any countable-target fold recovers
   the executor — "no compositional second reading" verbatim. Face 1 ⟹ face 2 is
   PROVED below (`conflation_blocks_decode`); the keystone conjoins both, so its
   TODO realizer is the one cardinality argument for face 1.
4. Stated at `σ := ℕ`, `δ : Type 0` — the minimal universe where the phenomenon
   lives; descriptor types are `Type 0` in practice, and nothing in the argument
   uses more.

This is why `Pred/` is a syntactic AST end-to-end: guards enter signatures as
countable CODES plus an eval, never as `σ → Bool` payloads in `Op`. -/

/-- Shapes of the canonical opaque signature: one guard leaf PER SEMANTIC PAYLOAD
`φ : σ → Bool` (the payload lives in the shape — this is what "opaque leaf" means),
and one sequencing node. -/
inductive OpaqueOp (σ : Type) : Type
  | guard (φ : σ → Bool)
  | seq

/-- The canonical opaque signature: guard leaves (empty arity) + one binary `seq`
node. The non-polynomial pattern N3 outlaws, isolated. -/
def OpaqueSig (σ : Type) : Signature where
  Op := OpaqueOp σ
  ar := fun s => match s with
    | .guard _ => Empty
    | .seq => Bool

/-- The guard-leaf term carrying payload `φ`. -/
def guardT {σ : Type} (φ : σ → Bool) : Term (OpaqueSig σ) :=
  .mk (.guard φ) nofun

/-- The sequencing node (`false` slot first, `true` slot second). -/
def seqT {σ : Type} (s t : Term (OpaqueSig σ)) : Term (OpaqueSig σ) :=
  .mk .seq fun b => bif b then t else s

/-- The EXECUTOR reading: carrier `σ → Bool`, guards mean themselves, `seq` means
conjunction ("both pass"). A genuine `Alg` — folds out of opaque signatures exist
just fine; what fails is faithful folds into SYNTAX. -/
def runAlg (σ : Type) : Alg (OpaqueSig σ) (σ → Bool) := fun s => match s with
  | .guard φ => fun _ => φ
  | .seq => fun k x => k false x && k true x

/-- The executor: the fold of `runAlg`. -/
def opaqueRun (σ : Type) : Term (OpaqueSig σ) → (σ → Bool) :=
  fold (runAlg σ)

@[simp]
theorem opaqueRun_guardT {σ : Type} (φ : σ → Bool) : opaqueRun σ (guardT φ) = φ :=
  rfl

@[simp]
theorem opaqueRun_seqT {σ : Type} (s t : Term (OpaqueSig σ)) (x : σ) :
    opaqueRun σ (seqT s t) x = (opaqueRun σ s x && opaqueRun σ t x) :=
  rfl

/-- The executor SEPARATES distinct guard payloads — the semantic reading uses
exactly the information a syntactic reading must lose. -/
theorem opaqueRun_separates_guards {σ : Type} {φ ψ : σ → Bool} (h : φ ≠ ψ) :
    opaqueRun σ (guardT φ) ≠ opaqueRun σ (guardT ψ) :=
  h

/-- **Face 1 — conflation.** Every fold of every algebra into every COUNTABLE
(= syntactic) target identifies two guard leaves with distinct payloads: there are
`2^ℵ₀` guard leaves and only countably many descriptors, so some pair the executor
separates gets one circuit. -/
def OpaqueConflation : Prop :=
  ∀ (δ : Type) [Countable δ] (alg : Alg (OpaqueSig ℕ) δ),
    ∃ φ ψ : ℕ → Bool, φ ≠ ψ ∧ fold alg (guardT φ) = fold alg (guardT ψ)

/-- **Face 2 — no compositional second reading.** No decoding of any fold into any
countable target recovers the executor: `decode ∘ fold alg ≠ opaqueRun` for every
`decode`. This is the verbatim "admits interpretations with no compositional second
reading": `opaqueRun` is an interpretation, and nothing compositional-through-syntax
computes it. -/
def NoFaithfulSyntacticReading : Prop :=
  ∀ (δ : Type) [Countable δ] (alg : Alg (OpaqueSig ℕ) δ)
    (decode : δ → (ℕ → Bool)),
    decode ∘ fold alg ≠ opaqueRun ℕ

/-- **[N3-converse] Syntactic leaves are FORCED** (KERNEL-NECESSITY §N3, converse
direction; breadstuffs negative precedent: `compile_not_a_seq_hom`): the canonical
opaque-payload signature admits interpretations (`opaqueRun`) with no faithful
compositional second reading into any syntactic target — conflation AND no-decode.
Contrapositive, which is how the tree consumes it: a signature that wants
derivation-totality (every second reading a faithful fold into syntax) must keep
its payloads syntactic — polynomial with countable `Op`.

ATLAS keystone fields (obligation, statement-first):
* satisfiable: `opaqueConflation_proved` realizes the cardinality face by Cantor's
  diagonal argument. If the guard-leaf reading were injective, composing it with
  a countable target's injection into `ℕ` and the characteristic-function injection
  `Set ℕ → (ℕ → Bool)` would contradict `Function.cantor_injective`.
  Non-injectivity is exactly `OpaqueConflation`, and `conflation_blocks_decode`
  finishes `NoFaithfulSyntacticReading`.
* teeth: rules out every "compile the closure-carrying IR to descriptors" design —
  the exact shape breadstuffs shipped (`RecStmt.guard` closures) and then had to
  prove uncompilable-as-a-fold (`compile_not_a_seq_hom`). Teeth exercised NOW at a
  concrete algebra: `conflation_shape_inhabited` + `conflated_pair_separated`
  exhibit a pair the executor separates and a countable-target fold conflates.
* premise-inhabitation: the quantified premises are inhabited — `δ := ℕ` is
  `Countable`, `constAlg : Alg (OpaqueSig ℕ) ℕ` is exhibited below; the `∀` is
  over a nonempty domain. -/
def N3_opaque_payloads_forbid_second_reading : Prop :=
  OpaqueConflation ∧ NoFaithfulSyntacticReading

#check N3_opaque_payloads_forbid_second_reading

/-- **Face 1 implies face 2** (proved glue — the keystone's realizer TODO reduces
to the cardinality face): a decoding that recovered the executor would make
`fold alg` injective on guard leaves, which conflation forbids. -/
theorem conflation_blocks_decode :
    OpaqueConflation → NoFaithfulSyntacticReading := by
  intro hC δ _ alg decode hdec
  obtain ⟨φ, ψ, hne, heq⟩ := hC δ alg
  apply hne
  calc φ = decode (fold alg (guardT φ)) := (congrFun hdec (guardT φ)).symm
    _ = decode (fold alg (guardT ψ)) := by rw [heq]
    _ = ψ := congrFun hdec (guardT ψ)

/-- **The cardinality face is realized.** A countable target supplies an injection
into `ℕ`. Were its guard-leaf fold injective, composing those maps with the
injective characteristic-function encoding `Set ℕ → (ℕ → Bool)` would inject
`Set ℕ` into `ℕ`, contradicting Cantor's theorem. -/
theorem opaqueConflation_proved : OpaqueConflation := by
  classical
  intro δ _ alg
  let readGuard : (ℕ → Bool) → δ := fun φ => fold alg (guardT φ)
  have hnot : ¬ Function.Injective readGuard := by
    intro hinj
    obtain ⟨encode, hencode⟩ := Countable.exists_injective_nat δ
    let characteristic : Set ℕ → (ℕ → Bool) := fun s n => decide (n ∈ s)
    have hcharacteristic : Function.Injective characteristic := by
      intro s t hst
      ext n
      constructor
      · intro hs
        by_contra ht
        have h := congrFun hst n
        simp [characteristic, hs, ht] at h
      · intro ht
        by_contra hs
        have h := congrFun hst n
        simp [characteristic, hs, ht] at h
    exact Function.cantor_injective (encode ∘ readGuard ∘ characteristic)
      (hencode.comp (hinj.comp hcharacteristic))
  obtain ⟨φ, ψ, heq, hne⟩ := Function.not_injective_iff.mp hnot
  exact ⟨φ, ψ, hne, heq⟩

/-- **[N3-converse], discharged.** Cantor forces conflation for every countable
compositional target, and that conflation rules out every decoder recovering the
opaque executor. -/
theorem N3_opaque_payloads_forbid_second_reading_proved :
    N3_opaque_payloads_forbid_second_reading :=
  ⟨opaqueConflation_proved, conflation_blocks_decode opaqueConflation_proved⟩

/-- Premise-inhabitation witness: a countable-target algebra exists (the constant
descriptor — every term compiles to `0`). -/
def constAlg : Alg (OpaqueSig ℕ) ℕ :=
  fun _ _ => 0

/-- The conflation SHAPE is inhabited at `constAlg` (this does NOT prove the `∀` of
`OpaqueConflation`; it shows the inner `∃`'s conflict is real on a concrete
countable-target fold): two distinct payloads, one descriptor. -/
theorem conflation_shape_inhabited :
    ∃ φ ψ : ℕ → Bool, φ ≠ ψ ∧
      fold constAlg (guardT φ) = fold constAlg (guardT ψ) := by
  refine ⟨fun _ => true, fun _ => false, fun h => ?_, rfl⟩
  exact Bool.noConfusion (congrFun h 0)

/-- ...and the executor SEPARATES that same conflated pair — the collapse the
obligation names, exercised end-to-end on one concrete instance. -/
theorem conflated_pair_separated :
    opaqueRun ℕ (guardT fun _ => true) ≠ opaqueRun ℕ (guardT fun _ => false) :=
  opaqueRun_separates_guards fun h => Bool.noConfusion (congrFun h 0)

end Minidregg.Compiler
