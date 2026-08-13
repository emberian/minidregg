/-
# `Theory/ZkmlTensorOps.lean` — the zkML tensor-op vocabulary, candidate-independent

## What this file is

The **shared object** of the zkML pillar: one indexed signature of tensor
operations, with a **denotation** — not an enum of op names. It is deliberately
the *intersection* vocabulary (catgrad ∩ catena, and whatever replaces either),
so it survives a tracer migration; and it names no field, no proof system, no
descriptor, so it survives an engine migration. `scripts/check-import-boundary.sh`
enforces the second half mechanically: Mathlib and `Theory/` only.

Modelled on `Theory/IndexedProgram.lean`, whose apparatus it instantiates rather
than re-derives:

* the typestate `Ix` is the **wire context** `Ctx = List TyT`; an operation is
  well-typed in a context and appends exactly one wire;
* `run` is `fold (denAlg S)` — the denotation IS a fold, so there is one program
  and two readings, never a spec/executable twin;
* **`run_transport`** (§7) is `fold_rel` applied once: two scalar readings related
  node-by-node are related on *every* trace, with **zero induction at the use
  site**;
* **`census_macs_eq_macAlg`** (§8) is `fold_fusion` applied once: the combined
  census's multiply-accumulate field *is* the standalone cost reading.

## The N3 constraint, and what it forced

`Compiler/Signature.lean`'s `[N3-converse]` (`opaqueConflation_proved`) proves by
Cantor that a signature whose constructor payloads are **semantic objects**
admits no faithful compositional second reading into any countable target. The
consequence here is not cosmetic: **no operation in this vocabulary carries tensor
data.** catgrad's trace has a `const` op carrying a digest of a weight blob; ours
has none. Every constant — model weight, bias, inference input — enters as an
entry of the *initial context* `Γ₀` and is referenced by a `Var`. Ops carry only
`ℕ`s, shapes, dtypes, function *ids*, and proofs. That is also the right
deployment shape: weights are a **commitment** surface (committed once, referenced
by index), not a per-inference **constraint** surface.

## What is deliberately NOT closed here

* `ScalarOps` is **law-free** — it supplies operations, not a ring. Field laws are
  the instantiating layer's business; nothing here assumes `select`'s formula
  collapses without them (`Selvage/`'s job, and the concrete witnesses in §9 do it
  at `ℤ` and `ZMod 7`).
* `bin .div`, `bin .pow`, `cmp`, `map`, `gather` and dtype-changing `cast` have
  **no reading forced by the ring structure**. `arith_transport` (§7.4) is proved
  exactly on the fragment that excludes them, and `TOp.arithmetic` is that
  fragment's decidable characteristic function. **That list is the arithmetization
  bill**, derived rather than asserted: it is what a `RingHom` fails to carry.
* Numeric adequacy (bf16 exactness, accumulator width, whether two float backends
  agree) is *not* addressed. This file fixes the *shape* of the reference reading
  and the *order* of every accumulation; which scalar semantics is adequate is a
  separate, open question.
* `slice`, `concat` and general (non-scalar) broadcast are **absent**, not
  stubbed. MNIST needs none of them; a KV cache needs `concat`. Adding them is
  adding constructors plus their denotation, and nothing in §7/§8 changes shape.
-/
import Mathlib.Tactic
import Mathlib.Logic.Equiv.Fin.Basic
import Theory.IndexedProgram

namespace Minidregg.Theory.ZkmlTensorOps

open Minidregg.Theory.IndexedProgram

/-! ## §1. Types: dtypes, shapes, multi-indices, values.

A shape is a `List ℕ` (outermost dimension first, row-major — pinned here and
nowhere else). `Idx s` is the *multi*-index of a shape, defined by recursion, so
`matmul`'s denotation needs no index arithmetic and no bound proofs. `idxEquiv`
is the canonical row-major linearization, and it is the *only* place the
row-major convention is used — a column-major deployment changes one definition.
-/

/-- Element types. `pred` is the 0/1-valued result of a comparison (carried in the
same scalar carrier, so `select` stays a degree-2 arithmetic formula); `idx` is an
integer address for `gather`. `bf16`/`f32`/`fp8` are the float widths the tracer
actually emits. -/
inductive Dtype
  | bf16 | f32 | fp8 | pred | idx
  deriving DecidableEq, Repr

/-- A tensor type: an element type plus a static shape. Static shapes are the
property that makes the whole trace geometry determined by the inputs; nothing
here can depend on tensor *data*. -/
structure TyT where
  dtype : Dtype
  shape : List ℕ
  deriving DecidableEq, Repr

/-- Element count of a shape. Defined by direct recursion (not `List.prod`) so
`size (n :: s) = n * size s` holds by `rfl`, which every dependent index below
relies on. -/
def size : List ℕ → ℕ
  | [] => 1
  | n :: s => n * size s

@[simp] theorem size_nil : size [] = 1 := rfl

@[simp] theorem size_cons (n : ℕ) (s : List ℕ) : size (n :: s) = n * size s := rfl

/-- The element count of a tensor type. -/
def TyT.numel (t : TyT) : ℕ := size t.shape

/-- The predicate type at the same shape — the result type of a comparison. -/
def TyT.pred (t : TyT) : TyT := ⟨Dtype.pred, t.shape⟩

@[simp] theorem TyT.pred_shape (t : TyT) : t.pred.shape = t.shape := rfl

/-- The **multi-index** of a shape: `Idx [m, n] = Fin m × Fin n × PUnit`. -/
def Idx : List ℕ → Type
  | [] => PUnit
  | n :: s => Fin n × Idx s

@[simp] theorem Idx_nil : Idx [] = PUnit := rfl

@[simp] theorem Idx_cons (n : ℕ) (s : List ℕ) : Idx (n :: s) = (Fin n × Idx s) := rfl

instance instDecidableEqIdx : ∀ s : List ℕ, DecidableEq (Idx s)
  | [] => inferInstanceAs (DecidableEq PUnit)
  | n :: s =>
      let _ := instDecidableEqIdx s
      inferInstanceAs (DecidableEq (Fin n × Idx s))

instance instFintypeIdx : ∀ s : List ℕ, Fintype (Idx s)
  | [] => inferInstanceAs (Fintype PUnit)
  | n :: s =>
      let _ := instFintypeIdx s
      inferInstanceAs (Fintype (Fin n × Idx s))

/-- **The row-major linearization**, as an `Equiv`. This is the single point at
which the memory-order convention is fixed; `reshape` and `broadcast` are the only
consumers. -/
def idxEquiv : ∀ s : List ℕ, Idx s ≃ Fin (size s)
  | [] =>
    { toFun := fun _ => ⟨0, Nat.zero_lt_one⟩
      invFun := fun _ => PUnit.unit
      left_inv := fun _ => rfl
      right_inv := fun i =>
        Fin.val_injective (Nat.lt_one_iff.mp i.isLt).symm }
  | n :: s => (Equiv.prodCongr (Equiv.refl (Fin n)) (idxEquiv s)).trans finProdFinEquiv

/-- Row-major **enumeration** of a shape's multi-indices. An emitter needs one
constraint per output element, so it needs this list. -/
def idxList : (s : List ℕ) → List (Idx s)
  | [] => [PUnit.unit]
  | n :: s => (List.finRange n).flatMap fun i => (idxList s).map fun j => (i, j)

/-- **The enumeration is total.** This is what makes "one constraint per element of
`idxList`" mean "every element constrained": an emitter that silently dropped an
index would be constraining a proper subset, and no theorem downstream would
notice. -/
theorem mem_idxList : ∀ {s : List ℕ} (i : Idx s), i ∈ idxList s := by
  intro s
  induction s with
  | nil => intro i; cases i; exact List.mem_singleton_self _
  | cons n s ih =>
      rintro ⟨i, j⟩
      simp only [idxList, List.mem_flatMap, List.mem_map]
      exact ⟨i, List.mem_finRange i, j, ih j, rfl⟩

/-- ...and it has exactly the element count the shape declares. -/
theorem length_idxList : ∀ s : List ℕ, (idxList s).length = size s := by
  intro s
  induction s with
  | nil => rfl
  | cons n s ih =>
      simp [idxList, List.length_flatMap, ih]

/-- A tensor **value** in carrier `α`: a total function from the type's
multi-index. Totality is the point — a shape error is not representable, so the
denotation below is total and needs no `Option`. -/
def TVal (α : Type) (t : TyT) : Type := Idx t.shape → α

/-- The **wire context**: the types of the wires in scope, most recent first. This
is the typestate index of the signature in §4. -/
abbrev Ctx := List TyT

/-- A wire reference — a de Bruijn index that carries its type. -/
inductive Var : Ctx → TyT → Type
  | here {Γ : Ctx} {t : TyT} : Var (t :: Γ) t
  | there {Γ : Ctx} {t u : TyT} : Var Γ t → Var (u :: Γ) t

/-- A value environment for a context. -/
inductive Env (α : Type) : Ctx → Type
  | nil : Env α []
  | cons {t : TyT} {Γ : Ctx} (v : TVal α t) (ρ : Env α Γ) : Env α (t :: Γ)

/-- Read a wire out of an environment. Total by construction. -/
def Env.get {α : Type} : {Γ : Ctx} → {t : TyT} → Env α Γ → Var Γ t → TVal α t
  | _, _, .cons v _, .here => v
  | _, _, .cons _ ρ, .there w => Env.get ρ w

/-! ## §2. The scalar reading — what an element type *means*, abstractly.

`ScalarOps α` is the parameter that makes the vocabulary candidate-independent: it
is what a "number" is. Note the shape of the record. `zero`/`one`/`un`/`bin` are
the ring-ish part; `cmpB`, `fn`, `cvt`, `toIdx` are the parts a field does **not**
determine. §7.4 proves that split is real rather than stylistic.
-/

/-- Elementwise unary kinds. Only `neg` is measured in the MNIST trace; reciprocal
is deliberately *not* here (it is `bin .div one`), so the vocabulary has one way to
say each thing. -/
inductive Un1
  | neg
  deriving DecidableEq, Repr

/-- Elementwise binary kinds. `div` and `pow` are present because the tracer emits
them (sigmoid decomposes to `neg → broadcast → cast → pow → add → div`); they are
also exactly the two that a ring homomorphism does not carry. -/
inductive Bin2
  | add | sub | mul | div | pow
  deriving DecidableEq, Repr

/-- Comparison kinds. A comparison has **no** reading forced by field structure —
it is a range/limb decomposition downstream, never a primitive. -/
inductive Cmp2
  | lt | le | eq
  deriving DecidableEq, Repr

/-- The identity of a pure unary map (`exp`, `sigmoid`, `tanh`, …), as a
**syntactic** id rather than a function payload — the `[N3-converse]` requirement.
At bf16 each such id is one 2^16-entry table. -/
abbrev FnId := ℕ

/-- **The scalar reading.** Everything the denotation needs to know about numbers,
and nothing else. Law-free on purpose: laws belong to the instantiating layer. -/
structure ScalarOps (α : Type) where
  zero : α
  one : α
  un : Un1 → α → α
  bin : Bin2 → α → α → α
  /-- Comparison — Boolean-valued, then encoded 0/1 into `α` by `TOp.denote`. -/
  cmpB : Cmp2 → α → α → Bool
  /-- The pure-map table family, indexed by the syntactic `FnId`. -/
  fn : FnId → α → α
  /-- Dtype conversion (rounding). `cvt d d` is *not* assumed to be the identity. -/
  cvt : Dtype → Dtype → α → α
  /-- Address extraction for `gather`. -/
  toIdx : α → ℕ

/-! ## §3. The operations.

Thirteen constructors, twenty-three distinct operations once the `Un1`/`Bin2`/
`Cmp2` kinds are counted. Every payload is `ℕ`, a `Dtype`, a shape, a `FnId`, a
`Var`, or a proof — **no tensor data, no functions** (§0, `[N3-converse]`).
-/

/-- The op vocabulary, indexed by the context it is well-typed in. Each op
produces exactly one new wire, whose type is `TOp.outTy`. -/
inductive TOp (Γ : Ctx) : Type
  /-- elementwise unary -/
  | un (k : Un1) (t : TyT) (a : Var Γ t) : TOp Γ
  /-- elementwise binary at **equal** types — there is no implicit broadcasting;
  `broadcast` is an explicit op, exactly as the tracer emits it -/
  | bin (k : Bin2) (t : TyT) (a b : Var Γ t) : TOp Γ
  /-- comparison, producing a `pred`-typed 0/1 tensor -/
  | cmp (k : Cmp2) (t : TyT) (a b : Var Γ t) : TOp Γ
  /-- `select s a b` — degree 2 and native to the sumcheck face -/
  | select (t : TyT) (s : Var Γ t.pred) (a b : Var Γ t) : TOp Γ
  /-- fused multiply-add `a*b + c` as ONE op: the rounding point is part of the
  vocabulary, not an accident of how a compiler contracted it -/
  | fma (t : TyT) (a b c : Var Γ t) : TOp Γ
  /-- a pure unary map, identified syntactically — the lookup-table class -/
  | map (f : FnId) (t : TyT) (a : Var Γ t) : TOp Γ
  /-- dtype conversion -/
  | cast (t : TyT) (a : Var Γ t) (d : Dtype) : TOp Γ
  /-- **matmul as an ordered fold**: `[m,k] · [k,n] → [m,n]`, contraction order
  specified (`List.finRange k`, left fold), so "accumulate exactly" is well-posed -/
  | matmul (d : Dtype) (m k n : ℕ)
      (a : Var Γ ⟨d, [m, k]⟩) (b : Var Γ ⟨d, [k, n]⟩) : TOp Γ
  /-- **ordered reduce** along the last axis, from an explicit initial wire -/
  | reduce (k : Bin2) (d : Dtype) (r c : ℕ)
      (init : Var Γ ⟨d, [r]⟩) (a : Var Γ ⟨d, [r, c]⟩) : TOp Γ
  /-- **index read** — a ROM/gather lookup at data-dependent addresses -/
  | gather (d : Dtype) (n m : ℕ)
      (tbl : Var Γ ⟨d, [n]⟩) (i : Var Γ ⟨Dtype.idx, [m]⟩) : TOp Γ
  /-- shape-only: `reshape`, carrying its own size-preservation proof -/
  | reshape (t : TyT) (a : Var Γ t) (s : List ℕ) (h : size s = size t.shape) : TOp Γ
  /-- shape-only: scalar `broadcast` (the only broadcast the tracer emits) -/
  | broadcast (t : TyT) (a : Var Γ t) (h : size t.shape = 1) (s : List ℕ) : TOp Γ
  /-- shape-only: 2-D `transpose` -/
  | transpose (d : Dtype) (m n : ℕ) (a : Var Γ ⟨d, [m, n]⟩) : TOp Γ

/-- The type of the wire an op produces. -/
def TOp.outTy {Γ : Ctx} : TOp Γ → TyT
  | .un _ t _ => t
  | .bin _ t _ _ => t
  | .cmp _ t _ _ => t.pred
  | .select t _ _ _ => t
  | .fma t _ _ _ => t
  | .map _ t _ => t
  | .cast t _ d => ⟨d, t.shape⟩
  | .matmul d m _ n _ _ => ⟨d, [m, n]⟩
  | .reduce _ d r _ _ _ => ⟨d, [r]⟩
  | .gather d _ m _ _ => ⟨d, [m]⟩
  | .reshape t _ s _ => ⟨t.dtype, s⟩
  | .broadcast t _ _ s => ⟨t.dtype, s⟩
  | .transpose d m n _ => ⟨d, [n, m]⟩

/-! ## §4. The denotation — the whole content of the vocabulary.

Every op is given a meaning in an arbitrary `ScalarOps α`. Two facts to read off
the definitions rather than take on trust:

* **`matmul` and `reduce` fold LEFT over `List.finRange`.** The accumulation order
  is part of the semantics. A non-associative scalar addition (which is what f32
  is) makes an unordered specification ill-posed; catena's `reducec` lowering
  makes the same choice, which is why the two vocabularies can agree.
* **`select` denotes the arithmetic formula** `s·a + (1−s)·b`, not an `if`. The two
  agree exactly when `s ∈ {0,1}`, which `cmp` guarantees by construction and which
  the constraint side must enforce with a booleanity gate. Denoting it as an `if`
  would have hidden that obligation inside the reference semantics.
-/

/-- **The denotation.** Total: a shape error is not representable. -/
def TOp.denote {α : Type} (S : ScalarOps α) {Γ : Ctx} :
    (op : TOp Γ) → Env α Γ → TVal α op.outTy
  | .un k _ a, ρ => fun i => S.un k (ρ.get a i)
  | .bin k _ a b, ρ => fun i => S.bin k (ρ.get a i) (ρ.get b i)
  | .cmp k _ a b, ρ => fun i =>
      if S.cmpB k (ρ.get a i) (ρ.get b i) then S.one else S.zero
  | .select _ s a b, ρ => fun i =>
      S.bin .add (S.bin .mul (ρ.get s i) (ρ.get a i))
        (S.bin .mul (S.bin .sub S.one (ρ.get s i)) (ρ.get b i))
  | .fma _ a b c, ρ => fun i =>
      S.bin .add (S.bin .mul (ρ.get a i) (ρ.get b i)) (ρ.get c i)
  | .map f _ a, ρ => fun i => S.fn f (ρ.get a i)
  | .cast t a d, ρ => fun i => S.cvt t.dtype d (ρ.get a i)
  | .matmul _ _ k _ a b, ρ => fun ij =>
      (List.finRange k).foldl
        (fun acc p =>
          S.bin .add acc
            (S.bin .mul (ρ.get a (ij.1, p, PUnit.unit)) (ρ.get b (p, ij.2.1, PUnit.unit))))
        S.zero
  | .reduce k _ _ c init a, ρ => fun i =>
      (List.finRange c).foldl
        (fun acc j => S.bin k acc (ρ.get a (i.1, j, PUnit.unit)))
        (ρ.get init i)
  | .gather _ n _ tbl idx, ρ => fun j =>
      if h : S.toIdx (ρ.get idx j) < n then ρ.get tbl (⟨_, h⟩, PUnit.unit) else S.zero
  | .reshape t a s h, ρ => fun i =>
      ρ.get a ((idxEquiv t.shape).symm (Fin.cast h ((idxEquiv s) i)))
  | .broadcast t a h _, ρ => fun _ =>
      ρ.get a ((idxEquiv t.shape).symm ⟨0, by omega⟩)
  | .transpose _ _ _ a, ρ => fun ji => ρ.get a (ji.2.1, ji.1, PUnit.unit)

/-! ## §5. The signature and the trace.

A **trace** is a `Program` over `tensorSig`: a straight-line sequence of ops, each
appending one wire, ending in a designated output wire. This is exactly the shape
the catgrad stager emits, and it is intrinsically typed — a trace that mentions a
wire of the wrong shape does not exist as a term.
-/

/-- The zkML op signature: typestate = wire context, one deterministic response,
and each op appends its output type. -/
def tensorSig : IxSignature Ctx where
  Op := TOp
  Resp := fun _ => Unit
  next := fun {Γ} op _ => op.outTy :: Γ

/-- A **trace** with declared output type `tOut`, over the initial context `Γ`
(the inputs and committed parameters). -/
abbrev Trace (tOut : TyT) (Γ : Ctx) : Type :=
  Program tensorSig (fun Γ' => Var Γ' tOut) Γ

/-- Append one op to the front of a trace. -/
def Trace.op {tOut : TyT} {Γ : Ctx} (o : TOp Γ)
    (rest : Trace tOut (o.outTy :: Γ)) : Trace tOut Γ :=
  .call o fun _ => rest

/-- Finish a trace at a designated output wire. -/
def Trace.ret {tOut : TyT} {Γ : Ctx} (w : Var Γ tOut) : Trace tOut Γ :=
  .pure w

/-! ## §6. Running a trace — the denotation IS a fold.

There is one program and two (or more) readings of it. There is no separate
"executable interpreter" that could drift, because the interpreter is
`fold denAlg` and every other reading is a fold of some other algebra over the
same signature.
-/

/-- The denotation algebra: extend the environment by each op's denoted value,
and read the designated wire at the end. -/
def denAlg {α : Type} (S : ScalarOps α) (tOut : TyT) :
    Algebra tensorSig (fun Γ => Var Γ tOut) (fun Γ => Env α Γ → TVal α tOut) where
  pure := fun w ρ => ρ.get w
  call := fun op k ρ => k () (Env.cons (op.denote S ρ) ρ)

/-- **Run a trace** at a scalar reading. -/
def run {α : Type} (S : ScalarOps α) {tOut : TyT} {Γ : Ctx}
    (p : Trace tOut Γ) (ρ : Env α Γ) : TVal α tOut :=
  fold (denAlg S tOut) p ρ

@[simp] theorem run_ret {α : Type} (S : ScalarOps α) {tOut : TyT} {Γ : Ctx}
    (w : Var Γ tOut) (ρ : Env α Γ) : run S (Trace.ret w) ρ = ρ.get w := rfl

@[simp] theorem run_op {α : Type} (S : ScalarOps α) {tOut : TyT} {Γ : Ctx}
    (o : TOp Γ) (rest : Trace tOut (o.outTy :: Γ)) (ρ : Env α Γ) :
    run S (Trace.op o rest) ρ = run S rest (Env.cons (o.denote S ρ) ρ) := rfl

/-! ## §7. Cross-reading agreement — `fold_rel`, once.

The reference numeric reading and the field reading are two `ScalarOps`. A
`ScalarHom` relates them node-by-node; `fold_rel` then relates them on **every**
trace. This is the whole reason for choosing the `IndexedProgram` template: the
spec/implementation twin is structurally impossible, because there is one
signature and two folds rather than two programs.
-/

/-- Two tensor values correspond under `φ`. -/
def TValRel {α β : Type} (φ : α → β) {t : TyT} (x : TVal α t) (y : TVal β t) : Prop :=
  ∀ i, φ (x i) = y i

/-- Two environments correspond under `φ`, wire by wire. -/
def EnvRel {α β : Type} (φ : α → β) : {Γ : Ctx} → Env α Γ → Env β Γ → Prop
  | _, .nil, .nil => True
  | _, .cons x ρ, .cons y σ => TValRel φ x y ∧ EnvRel φ ρ σ

/-- **A morphism of scalar readings.** Note what it demands: `cmpB` must agree as
a *Boolean* (not merely up to `φ`), and `toIdx` must agree as a *natural number*.
Those two fields are where a "compatible field reading" stops being free. -/
structure ScalarHom {α β : Type} (φ : α → β) (S : ScalarOps α) (T : ScalarOps β) :
    Prop where
  zero : φ S.zero = T.zero
  one : φ S.one = T.one
  un : ∀ k a, φ (S.un k a) = T.un k (φ a)
  bin : ∀ k a b, φ (S.bin k a b) = T.bin k (φ a) (φ b)
  cmpB : ∀ k a b, S.cmpB k a b = T.cmpB k (φ a) (φ b)
  fn : ∀ f a, φ (S.fn f a) = T.fn f (φ a)
  cvt : ∀ d d' a, φ (S.cvt d d' a) = T.cvt d d' (φ a)
  toIdx : ∀ a, S.toIdx a = T.toIdx (φ a)

/-- Reading a wire respects the environment relation. -/
theorem envRel_get {α β : Type} {φ : α → β} :
    ∀ {Γ : Ctx} {t : TyT} (w : Var Γ t) {ρ : Env α Γ} {σ : Env β Γ},
      EnvRel φ ρ σ → TValRel φ (ρ.get w) (σ.get w) := by
  intro Γ t w
  induction w with
  | here => intro ρ σ h; cases ρ; cases σ; exact h.1
  | there _ ih => intro ρ σ h; cases ρ; cases σ; exact ih h.2

/-- A left fold transports along a map that commutes with the step function. Used
by `matmul` and `reduce`, whose accumulation order is specified — this is where
"the order is part of the semantics" is cashed in: the lemma is about `foldl`, and
there is no unordered version of it to reach for. -/
theorem foldl_hom {α β γ : Type} (φ : α → β) (F : α → γ → α) (G : β → γ → β)
    (hFG : ∀ (a : α) (b : β) (c : γ), φ a = b → φ (F a c) = G b c) :
    ∀ (l : List γ) (z : α) (w : β), φ z = w → φ (l.foldl F z) = l.foldl G w := by
  intro l
  induction l with
  | nil => intro _ _ hzw; exact hzw
  | cons c l ih => intro z w hzw; exact ih (F z c) (G w c) (hFG z w c hzw)

/-- **The per-op transport lemma** — the only place the thirteen constructors are
enumerated. Everything above the op level is generic. -/
theorem denote_op_rel {α β : Type} {φ : α → β} {S : ScalarOps α} {T : ScalarOps β}
    (hom : ScalarHom φ S T) {Γ : Ctx} (op : TOp Γ) {ρ : Env α Γ} {σ : Env β Γ}
    (h : EnvRel φ ρ σ) : TValRel φ (op.denote S ρ) (op.denote T σ) := by
  cases op with
  | un k t a => intro i; simp only [TOp.denote, hom.un, envRel_get a h i]
  | bin k t a b =>
      intro i
      simp only [TOp.denote, hom.bin, envRel_get a h i, envRel_get b h i]
  | cmp k t a b =>
      intro i
      simp only [TOp.denote]
      rw [← envRel_get a h i, ← envRel_get b h i, ← hom.cmpB]
      by_cases hc : S.cmpB k (ρ.get a i) (ρ.get b i) = true
      · rw [if_pos hc, if_pos hc]; exact hom.one
      · rw [if_neg hc, if_neg hc]; exact hom.zero
  | select t s a b =>
      intro i
      simp only [TOp.denote, hom.bin, hom.one, envRel_get s h i, envRel_get a h i,
        envRel_get b h i]
  | fma t a b c =>
      intro i
      simp only [TOp.denote, hom.bin, envRel_get a h i, envRel_get b h i,
        envRel_get c h i]
  | map f t a => intro i; simp only [TOp.denote, hom.fn, envRel_get a h i]
  | cast t a d => intro i; simp only [TOp.denote, hom.cvt, envRel_get a h i]
  | matmul d m k n a b =>
      intro ij
      simp only [TOp.denote]
      have hstep : ∀ (acc : α) (bb : β) (p : Fin k), φ acc = bb →
          φ (S.bin .add acc
                (S.bin .mul (ρ.get a (ij.1, p, PUnit.unit)) (ρ.get b (p, ij.2.1, PUnit.unit))))
            = T.bin .add bb
                (T.bin .mul (σ.get a (ij.1, p, PUnit.unit)) (σ.get b (p, ij.2.1, PUnit.unit))) := by
        intro acc bb p hb
        rw [hom.bin, hom.bin, hb, envRel_get a h (ij.1, p, PUnit.unit),
          envRel_get b h (p, ij.2.1, PUnit.unit)]
      exact foldl_hom φ _ _ hstep (List.finRange k) S.zero T.zero hom.zero
  | reduce k d r c init a =>
      intro i
      simp only [TOp.denote]
      have hstep : ∀ (acc : α) (bb : β) (j : Fin c), φ acc = bb →
          φ (S.bin k acc (ρ.get a (i.1, j, PUnit.unit)))
            = T.bin k bb (σ.get a (i.1, j, PUnit.unit)) := by
        intro acc bb j hb
        rw [hom.bin, hb, envRel_get a h (i.1, j, PUnit.unit)]
      exact foldl_hom φ _ _ hstep (List.finRange c) _ _ (envRel_get init h i)
  | gather d n m tbl idx =>
      intro j
      simp only [TOp.denote]
      rw [← envRel_get idx h j, ← hom.toIdx]
      by_cases hc : S.toIdx (ρ.get idx j) < n
      · rw [dif_pos hc, dif_pos hc]; exact envRel_get tbl h _
      · rw [dif_neg hc, dif_neg hc]; exact hom.zero
  | reshape t a s hs => intro i; exact envRel_get a h _
  | broadcast t a hb s => intro _; exact envRel_get a h _
  | transpose d m n a => intro ji; exact envRel_get a h _

/-- The cross-carrier relation on denotation carriers: related environments give
related outputs. -/
def denRel {α β : Type} (φ : α → β) (tOut : TyT) (Γ : Ctx)
    (f : Env α Γ → TVal α tOut) (g : Env β Γ → TVal β tOut) : Prop :=
  ∀ ρ σ, EnvRel φ ρ σ → TValRel φ (f ρ) (g σ)

/-- The two denotation algebras preserve `denRel` node by node. -/
theorem denAlgRel {α β : Type} {φ : α → β} {S : ScalarOps α} {T : ScalarOps β}
    (hom : ScalarHom φ S T) (tOut : TyT) :
    AlgebraRel (denAlg S tOut) (denAlg T tOut) (denRel φ tOut) where
  pure := fun w _ _ h => envRel_get w h
  call := fun op _ _ hk _ _ h =>
    hk () _ _ ⟨denote_op_rel hom op h, h⟩

/-- **`run_transport` — the keystone.** Two scalar readings related by a
`ScalarHom` produce corresponding results on **every** trace, from corresponding
environments. `fold_rel` does the induction once, generically; there is none here
and none at any use site. -/
theorem run_transport {α β : Type} {φ : α → β} {S : ScalarOps α} {T : ScalarOps β}
    (hom : ScalarHom φ S T) {tOut : TyT} {Γ : Ctx} (p : Trace tOut Γ)
    {ρ : Env α Γ} {σ : Env β Γ} (h : EnvRel φ ρ σ) :
    TValRel φ (run S p ρ) (run T p σ) :=
  fold_rel (denAlgRel hom tOut) p ρ σ h

/-! ### §7.1 Premise inhabitation — `ScalarHom` is not an empty hypothesis.

The doubled reading runs the same trace in `α × α`. The diagonal is a `ScalarHom`
at *every* field of the record including `div`, `pow`, `cmpB` and `toIdx`, so the
hypothesis of `run_transport` is inhabited non-trivially (φ is not the identity,
and the carriers differ). -/

/-- The doubled scalar reading — two lockstep evaluations in one carrier. -/
def ScalarOps.dup {α : Type} (S : ScalarOps α) : ScalarOps (α × α) where
  zero := (S.zero, S.zero)
  one := (S.one, S.one)
  un := fun k a => (S.un k a.1, S.un k a.2)
  bin := fun k a b => (S.bin k a.1 b.1, S.bin k a.2 b.2)
  cmpB := fun k a b => S.cmpB k a.1 b.1
  fn := fun f a => (S.fn f a.1, S.fn f a.2)
  cvt := fun d d' a => (S.cvt d d' a.1, S.cvt d d' a.2)
  toIdx := fun a => S.toIdx a.1

/-- The diagonal is a morphism of scalar readings — premise inhabitation for
`run_transport`, at a genuinely different carrier. -/
theorem diag_hom {α : Type} (S : ScalarOps α) :
    ScalarHom (fun a => (a, a)) S S.dup := by
  constructor <;> intros <;> rfl

/-! ### §7.2 The fragment a ring homomorphism actually carries.

`ScalarHom` is a strong hypothesis, and the interesting instantiation — the exact
integer reference reading against the prover field — does **not** satisfy it. The
honest theorem is the restricted one, and the restriction is *derived*: it is
exactly the set of ops whose reading is not forced by `+`, `−`, `×`, `0`, `1`. -/

/-- The **arithmetic fragment**: ops whose meaning is fixed by the ring structure
alone. Everything excluded here is an item on the arithmetization bill —
`div` and `pow` (witnessed inverse / exponent gadget), `cmp` (range or limb
decomposition), `map` (a lookup table), `gather` (a ROM bus), and a *dtype-changing*
`cast` (a rounding relation). -/
def TOp.arithmetic {Γ : Ctx} : TOp Γ → Bool
  | .bin k _ _ _ => match k with
      | .add | .sub | .mul => true
      | .div | .pow => false
  | .cmp _ _ _ _ => false
  | .map _ _ _ => false
  | .gather _ _ _ _ _ => false
  | .cast t _ d => decide (t.dtype = d)
  | .reduce k _ _ _ _ _ => match k with
      | .add | .sub | .mul => true
      | .div | .pow => false
  | _ => true

/-- A trace lies in the arithmetic fragment when every op does. -/
def Trace.arithmetic {tOut : TyT} : {Γ : Ctx} → Trace tOut Γ → Prop
  | _, .pure _ => True
  | _, .call op k => op.arithmetic = true ∧ ∀ r, Trace.arithmetic (k r)

/-- A scalar reading is **ring-shaped** when its `0`, `1`, `neg`, `add`, `sub`,
`mul` and identity `cvt` are the carrier's ring operations. This is a property of
the *reading*, not of the vocabulary. -/
structure IsRingReading {α : Type} [Ring α] (S : ScalarOps α) : Prop where
  zero : S.zero = 0
  one : S.one = 1
  neg : ∀ a, S.un .neg a = -a
  add : ∀ a b, S.bin .add a b = a + b
  sub : ∀ a b, S.bin .sub a b = a - b
  mul : ∀ a b, S.bin .mul a b = a * b
  cvt_id : ∀ d a, S.cvt d d a = a

/-- Ring readings transport along a ring homomorphism on the ops the ring
structure determines. -/
theorem ringHom_denote_op {α β : Type} [Ring α] [Ring β] (ψ : α →+* β)
    {S : ScalarOps α} {T : ScalarOps β} (hS : IsRingReading S) (hT : IsRingReading T)
    {Γ : Ctx} (op : TOp Γ) (harith : op.arithmetic = true)
    {ρ : Env α Γ} {σ : Env β Γ} (h : EnvRel (ψ : α → β) ρ σ) :
    TValRel (ψ : α → β) (op.denote S ρ) (op.denote T σ) := by
  cases op with
  | un k t a =>
      cases k
      intro i; simp [TOp.denote, hS.neg, hT.neg, envRel_get a h i]
  | bin k t a b =>
      intro i
      cases k <;>
        simp_all [TOp.denote, hS.add, hT.add, hS.sub, hT.sub, hS.mul, hT.mul,
          envRel_get a h i, envRel_get b h i, TOp.arithmetic]
  | cmp k t a b => simp [TOp.arithmetic] at harith
  | select t s a b =>
      intro i
      simp [TOp.denote, hS.add, hT.add, hS.sub, hT.sub, hS.mul, hT.mul, hS.one,
        hT.one, envRel_get s h i, envRel_get a h i, envRel_get b h i]
  | fma t a b c =>
      intro i
      simp [TOp.denote, hS.add, hT.add, hS.mul, hT.mul, envRel_get a h i,
        envRel_get b h i, envRel_get c h i]
  | map f t a => simp [TOp.arithmetic] at harith
  | cast t a d =>
      have hd : t.dtype = d := by simpa [TOp.arithmetic] using harith
      subst hd
      intro i; simp [TOp.denote, hS.cvt_id, hT.cvt_id, envRel_get a h i]
  | matmul d m k n a b =>
      intro ij
      simp only [TOp.denote]
      have hstep : ∀ (acc : α) (bb : β) (p : Fin k), ψ acc = bb →
          ψ (S.bin .add acc
                (S.bin .mul (ρ.get a (ij.1, p, PUnit.unit)) (ρ.get b (p, ij.2.1, PUnit.unit))))
            = T.bin .add bb
                (T.bin .mul (σ.get a (ij.1, p, PUnit.unit)) (σ.get b (p, ij.2.1, PUnit.unit))) := by
        intro acc bb p hb
        rw [hS.add, hT.add, hS.mul, hT.mul, map_add, map_mul, hb,
          envRel_get a h (ij.1, p, PUnit.unit), envRel_get b h (p, ij.2.1, PUnit.unit)]
      refine foldl_hom (ψ : α → β) _ _ hstep (List.finRange k) S.zero T.zero ?_
      rw [hS.zero, hT.zero, map_zero]
  | reduce k d r c init a =>
      intro i
      simp only [TOp.denote]
      have hstep : ∀ (acc : α) (bb : β) (j : Fin c), ψ acc = bb →
          ψ (S.bin k acc (ρ.get a (i.1, j, PUnit.unit)))
            = T.bin k bb (σ.get a (i.1, j, PUnit.unit)) := by
        intro acc bb j hb
        have haj := envRel_get a h (i.1, j, PUnit.unit)
        cases k <;>
          simp_all [hS.add, hT.add, hS.sub, hT.sub, hS.mul, hT.mul, TOp.arithmetic]
      exact foldl_hom (ψ : α → β) _ _ hstep (List.finRange c) _ _ (envRel_get init h i)
  | gather d n m tbl idx => simp [TOp.arithmetic] at harith
  | reshape t a s hs => intro i; exact envRel_get a h _
  | broadcast t a hb s => intro _; exact envRel_get a h _
  | transpose d m n a => intro ji; exact envRel_get a h _

/-- **`arith_transport` — the reference reading and the field reading agree on the
arithmetic fragment.** This is the zkML statement in its honest form: an exact
integer reference computation and the prover-field computation of the *same trace*
give corresponding answers, provided the trace uses only ops the ring structure
determines. The ops it excludes are precisely the gadget bill. -/
theorem arith_transport {α β : Type} [Ring α] [Ring β] (ψ : α →+* β)
    {S : ScalarOps α} {T : ScalarOps β} (hS : IsRingReading S) (hT : IsRingReading T)
    {tOut : TyT} : ∀ {Γ : Ctx} (p : Trace tOut Γ), p.arithmetic →
      ∀ {ρ : Env α Γ} {σ : Env β Γ}, EnvRel (ψ : α → β) ρ σ →
        TValRel (ψ : α → β) (run S p ρ) (run T p σ) := by
  intro Γ p
  induction p with
  | pure w => intro _ ρ σ h; exact envRel_get w h
  | call op k ih =>
      intro harith ρ σ h
      exact ih () (harith.2 ()) ⟨ringHom_denote_op ψ hS hT op harith.1 h, h⟩

/-! ## §8. A second reading of the same signature — the cost census, by fusion.

The census reproduces the tracer's own measured numbers *inside Lean*, from the
intrinsically typed trace rather than from the JSON. `fold_fusion` then says the
census's multiply-accumulate field IS the standalone cost reading — one theorem,
no induction at the use site. -/

/-- The cost census of a trace. `outElems` is the total number of produced scalar
elements — the commitment surface; `macs` is the multiply-accumulate count — the
constraint surface. The memo's measured MNIST run separates these two for a
reason: conflating them inflates the circuit by 20×. -/
structure Census where
  ops : ℕ
  macs : ℕ
  outElems : ℕ
  deriving DecidableEq, Repr

/-- Multiply-accumulates charged by one op. Matmul is `m·k·n`; an ordered reduce
is `r·c`; `fma` and elementwise `mul` are one per element; everything else is
zero. -/
def TOp.macs {Γ : Ctx} : TOp Γ → ℕ
  | .matmul _ m k n _ _ => m * k * n
  | .reduce _ _ r c _ _ => r * c
  | .fma t _ _ _ => size t.shape
  | .bin k t _ _ => match k with
      | .mul => size t.shape
      | _ => 0
  | _ => 0

/-- The census reading. -/
def censusAlg (tOut : TyT) :
    Algebra tensorSig (fun Γ => Var Γ tOut) (fun _ => Census) where
  pure := fun _ => ⟨0, 0, 0⟩
  call := fun op k =>
    ⟨(k ()).ops + 1, (k ()).macs + op.macs, (k ()).outElems + size op.outTy.shape⟩

/-- The standalone multiply-accumulate reading. -/
def macAlg (tOut : TyT) :
    Algebra tensorSig (fun Γ => Var Γ tOut) (fun _ => ℕ) where
  pure := fun _ => 0
  call := fun op k => k () + op.macs

/-- Projecting the census onto its cost field is an algebra morphism. -/
def censusMacHom (tOut : TyT) :
    AlgebraHom (censusAlg tOut) (macAlg tOut) (fun _ c => c.macs) where
  pure := by intro _ _; rfl
  call := by intro _ _ _; rfl

/-- **`census_macs_eq_macAlg`** — by `fold_fusion`: the combined census agrees with
the standalone cost reading on every trace, with no induction at the use site. -/
theorem census_macs_eq_macAlg (tOut : TyT) {Γ : Ctx} (p : Trace tOut Γ) :
    (fold (censusAlg tOut) p).macs = fold (macAlg tOut) p :=
  fold_fusion (censusMacHom tOut) p

/-- Census of a trace. -/
def census {tOut : TyT} {Γ : Ctx} (p : Trace tOut Γ) : Census :=
  fold (censusAlg tOut) p

/-- A third reading of the same signature: how many ops fall **outside** the
arithmetic fragment, i.e. how many gadgets a trace costs. -/
def gadgetAlg (tOut : TyT) :
    Algebra tensorSig (fun Γ => Var Γ tOut) (fun _ => ℕ) where
  pure := fun _ => 0
  call := fun op k => k () + (if op.arithmetic then 0 else 1)

/-- The gadget count of a trace. -/
def gadgetCount {tOut : TyT} {Γ : Ctx} (p : Trace tOut Γ) : ℕ :=
  fold (gadgetAlg tOut) p

/-- **The count is a certificate, not a statistic.** A trace costs zero gadgets
exactly when it lies in the arithmetic fragment — so `gadgetCount p = 0`, which is
computable, discharges `arith_transport`'s hypothesis, which is not. -/
theorem gadgetCount_eq_zero_iff {tOut : TyT} :
    ∀ {Γ : Ctx} (p : Trace tOut Γ), gadgetCount p = 0 ↔ p.arithmetic := by
  intro Γ p
  induction p with
  | pure w => exact ⟨fun _ => trivial, fun _ => rfl⟩
  | call op k ih =>
      show fold (gadgetAlg tOut) (k ()) + (if op.arithmetic then 0 else 1) = 0 ↔ _
      rw [Nat.add_eq_zero_iff]
      constructor
      · rintro ⟨hk, ho⟩
        refine ⟨?_, fun r => ?_⟩
        · by_cases h : op.arithmetic = true
          · exact h
          · simp [h] at ho
        · cases r; exact (ih ()).mp hk
      · rintro ⟨ho, hk⟩
        exact ⟨(ih ()).mpr (hk ()), by simp [ho]⟩

/-- A **deliberately wrong** cost reading: it charges a matmul `m·n`, forgetting
the contraction. This is the mistake that would price an MNIST circuit 784× cheap,
so it is the one worth having a tooth for. -/
def wrongMacAlg (tOut : TyT) :
    Algebra tensorSig (fun Γ => Var Γ tOut) (fun _ => ℕ) where
  pure := fun _ => 0
  call := fun op k => k () + (match op with
    | .matmul _ m _ n _ _ => m * n
    | o => o.macs)

/-! ## §9. Concrete readings, computed witnesses, and teeth.

Nothing above is allowed to stand on inspection. This section instantiates the
vocabulary at `ℤ` and at `ZMod 7`, computes a real matmul, and exhibits three
teeth: a wrong cost algebra, a wrong scalar reading, and the div/pow gap. -/

/-- The **exact integer reading**. `div`/`pow`/`cmpB`/`fn`/`cvt`/`toIdx` are
supplied as parameters rather than chosen here — the signature is the statement
that these six are not determined by the ring. -/
def intOps (dv : ℤ → ℤ → ℤ) (pw : ℤ → ℤ → ℤ) (tbl : FnId → ℤ → ℤ) : ScalarOps ℤ where
  zero := 0
  one := 1
  un := fun _ a => -a
  bin := fun k a b => match k with
    | .add => a + b
    | .sub => a - b
    | .mul => a * b
    | .div => dv a b
    | .pow => pw a b
  cmpB := fun k a b => match k with
    | .lt => decide (a < b)
    | .le => decide (a ≤ b)
    | .eq => decide (a = b)
  fn := tbl
  cvt := fun _ _ a => a
  toIdx := fun a => a.toNat

theorem intOps_isRingReading (dv pw : ℤ → ℤ → ℤ) (tbl : FnId → ℤ → ℤ) :
    IsRingReading (intOps dv pw tbl) := by
  constructor <;> intros <;> rfl

/-- The **field reading**, at an arbitrary commutative ring. Again the six
undetermined operations are parameters. -/
def ringOps (α : Type) [Ring α] (dv : α → α → α) (pw : α → α → α)
    (cmp : Cmp2 → α → α → Bool) (tbl : FnId → α → α) (ix : α → ℕ) : ScalarOps α where
  zero := 0
  one := 1
  un := fun _ a => -a
  bin := fun k a b => match k with
    | .add => a + b
    | .sub => a - b
    | .mul => a * b
    | .div => dv a b
    | .pow => pw a b
  cmpB := cmp
  fn := tbl
  cvt := fun _ _ a => a
  toIdx := ix

theorem ringOps_isRingReading (α : Type) [Ring α] (dv pw : α → α → α)
    (cmp : Cmp2 → α → α → Bool) (tbl : FnId → α → α) (ix : α → ℕ) :
    IsRingReading (ringOps α dv pw cmp tbl ix) := by
  constructor <;> intros <;> rfl

/-! ### §9.1 A trace that computes: a 2×3 · 3×2 matmul. -/

/-- `f32` at shape `[2,3]`. -/
def tA : TyT := ⟨Dtype.f32, [2, 3]⟩
/-- `f32` at shape `[3,2]`. -/
def tB : TyT := ⟨Dtype.f32, [3, 2]⟩
/-- `f32` at shape `[2,2]`. -/
def tC : TyT := ⟨Dtype.f32, [2, 2]⟩

/-- The initial context: the two operands, `A` at `here`. -/
def mmCtx : Ctx := [tA, tB]

/-- One matmul and return. -/
def mmTrace : Trace tC mmCtx :=
  Trace.op (TOp.matmul Dtype.f32 2 3 2 Var.here (Var.there Var.here))
    (Trace.ret Var.here)

/-- `A = [[1,2,3],[4,5,6]]`. -/
def aVal : TVal ℤ tA := fun i => (![![1, 2, 3], ![4, 5, 6]] : Fin 2 → Fin 3 → ℤ) i.1 i.2.1

/-- `B = [[1,0],[0,1],[1,1]]`. -/
def bVal : TVal ℤ tB := fun i => (![![1, 0], ![0, 1], ![1, 1]] : Fin 3 → Fin 2 → ℤ) i.1 i.2.1

/-- The environment holding both operands. -/
def mmEnv : Env ℤ mmCtx := Env.cons aVal (Env.cons bVal Env.nil)

/-- An arbitrary but fixed integer reading for the witnesses below (`div` is
truncating, `pow` is by `toNat`, the table family is the identity). -/
def zOps : ScalarOps ℤ := intOps (· / ·) (fun a b => a ^ b.toNat) (fun _ a => a)

/-- **Computed witness**: the matmul denotes `[[4,5],[10,11]]`, kernel-decided.
The trace runs; the vocabulary is not a picture of a vocabulary. -/
theorem mmTrace_computes :
    run zOps mmTrace mmEnv (0, 0, PUnit.unit) = 4 ∧
    run zOps mmTrace mmEnv (0, 1, PUnit.unit) = 5 ∧
    run zOps mmTrace mmEnv (1, 0, PUnit.unit) = 10 ∧
    run zOps mmTrace mmEnv (1, 1, PUnit.unit) = 11 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **Computed witness**: the census of that trace — one op, `2·3·2 = 12`
multiply-accumulates, four output elements. -/
theorem mmTrace_census : census mmTrace = ⟨1, 12, 4⟩ := by decide

/-- **Tooth 1 — the wrong cost reading is caught.** Charging a matmul `m·n`
instead of `m·k·n` gives `4` against `12`; the census is not free to be any
number. -/
theorem wrong_macs_mismatch :
    (census mmTrace).macs ≠ fold (wrongMacAlg tC) mmTrace := by decide

/-- The transport of the census through `fold_fusion`, on this trace. -/
theorem mmTrace_fusion : (census mmTrace).macs = fold (macAlg tC) mmTrace :=
  census_macs_eq_macAlg tC mmTrace

/-! ### §9.2 The scalar reading is load-bearing: two teeth. -/

/-- A **deliberately wrong** integer reading: subtraction read as addition. -/
def zOpsWrong : ScalarOps ℤ :=
  { zOps with bin := fun k a b => match k with
      | .add => a + b
      | .sub => a + b
      | .mul => a * b
      | .div => a / b
      | .pow => a ^ b.toNat }

/-- A trace using subtraction: `A - A` at shape `[2,3]`. -/
def subTrace : Trace tA mmCtx :=
  Trace.op (TOp.bin Bin2.sub tA Var.here Var.here) (Trace.ret Var.here)

/-- **Tooth 2 — sharing the syntax supplies no agreement.** The correct reading
gives `0`; the reading that mis-denotes `sub` gives `2`. A vocabulary is its
denotation, not its constructor names. -/
theorem wrong_scalar_mismatch :
    run zOps subTrace mmEnv (0, 0, PUnit.unit) ≠
      run zOpsWrong subTrace mmEnv (0, 0, PUnit.unit) := by decide

/-- `subTrace` is in the arithmetic fragment... -/
theorem subTrace_arithmetic : subTrace.arithmetic := ⟨rfl, fun _ => trivial⟩

/-- ...and so is the matmul trace, so `arith_transport` applies to both. -/
theorem mmTrace_arithmetic : mmTrace.arithmetic := ⟨rfl, fun _ => trivial⟩

/-- A trace using division — `A / A`. -/
def divTrace : Trace tA mmCtx :=
  Trace.op (TOp.bin Bin2.div tA Var.here Var.here) (Trace.ret Var.here)

/-- **Tooth 3 — the arithmetic fragment is a real restriction.** `divTrace` is
*not* in the fragment, and the reason is `div` and nothing else. Together with
tooth 2 this pins `TOp.arithmetic`: it is neither always true (this) nor always
false (`subTrace_arithmetic`). -/
theorem divTrace_not_arithmetic : ¬ divTrace.arithmetic := by
  rintro ⟨h, -⟩
  exact absurd h (by decide)

/-- A second integer reading that differs **only** in `div`. -/
def zOpsOtherDiv : ScalarOps ℤ := intOps (fun a _ => a) (fun a b => a ^ b.toNat) (fun _ a => a)

/-- **The div gap, exhibited.** The two readings agree on the whole arithmetic
fragment (they are the same ring reading), and disagree on a one-op division
trace. `run_transport`'s hypothesis is therefore not decoration: drop the `bin`
field for `div` and the conclusion is false. -/
theorem div_reading_disagrees :
    run zOps divTrace mmEnv (0, 1, PUnit.unit) ≠
      run zOpsOtherDiv divTrace mmEnv (0, 1, PUnit.unit) := by decide

/-- ...while on the *arithmetic* trace they agree — computed, on the same pair of
readings that disagree above. This is the fragment boundary, exhibited on one
pair rather than argued. -/
theorem arith_reading_agrees :
    run zOps mmTrace mmEnv (1, 1, PUnit.unit) =
      run zOpsOtherDiv mmTrace mmEnv (1, 1, PUnit.unit) := by decide

/-! ### §9.3 The transport, instantiated.

`ℤ →+* ZMod 7` carries the arithmetic fragment. This is the shape the deployment
needs: an exact integer reference computation and the prover-field computation of
one trace, proved to correspond, with the field never having been asked what
division or comparison mean. -/

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The `ZMod 7` reading, with the six undetermined operations supplied. -/
def z7Ops : ScalarOps (ZMod 7) :=
  ringOps (ZMod 7) (· / ·) (fun a b => a ^ b.val) (fun _ _ _ => false) (fun _ a => a)
    (fun a => a.val)

/-- The environment `mmEnv` read into `ZMod 7`. -/
def mmEnv7 : Env (ZMod 7) mmCtx :=
  Env.cons (fun i => ((aVal i : ℤ) : ZMod 7)) (Env.cons (fun i => ((bVal i : ℤ) : ZMod 7)) Env.nil)

theorem mmEnv_rel : EnvRel ((Int.castRingHom (ZMod 7) : ℤ →+* ZMod 7) : ℤ → ZMod 7) mmEnv mmEnv7 :=
  ⟨fun _ => rfl, fun _ => rfl, trivial⟩

/-- **The instantiated transport.** The integer matmul and the `ZMod 7` matmul of
the same trace correspond, by `arith_transport` — no induction, no per-op
argument, and no assumption about what `/` means in `ZMod 7`. -/
theorem mmTrace_transport :
    TValRel ((Int.castRingHom (ZMod 7) : ℤ →+* ZMod 7) : ℤ → ZMod 7)
      (run zOps mmTrace mmEnv) (run z7Ops mmTrace mmEnv7) :=
  arith_transport (Int.castRingHom (ZMod 7)) (intOps_isRingReading _ _ _)
    (ringOps_isRingReading _ _ _ _ _ _) mmTrace mmTrace_arithmetic mmEnv_rel

/-- ...and it says something: `11 ↦ 4` in `ZMod 7`, computed on both sides. -/
theorem mmTrace_transport_computes :
    run z7Ops mmTrace mmEnv7 (1, 1, PUnit.unit) = 4 := by decide

/-! ## §10. Axiom accounting.

Guarded footprints, so a later change that reaches for `native_decide` (which
would add `Lean.ofReduceBool`) or leaves a hole (`sorryAx`) turns the build red
instead of passing quietly. Every witness in §9 is kernel-decided. -/

/-- info: 'Minidregg.Theory.ZkmlTensorOps.run_transport' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_transport

/-- info: 'Minidregg.Theory.ZkmlTensorOps.arith_transport' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms arith_transport

/-- info: 'Minidregg.Theory.ZkmlTensorOps.census_macs_eq_macAlg' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms census_macs_eq_macAlg

/-- info: 'Minidregg.Theory.ZkmlTensorOps.mmTrace_transport' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mmTrace_transport

/-- info: 'Minidregg.Theory.ZkmlTensorOps.mmTrace_computes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mmTrace_computes

/-- info: 'Minidregg.Theory.ZkmlTensorOps.wrong_macs_mismatch' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_macs_mismatch

end Minidregg.Theory.ZkmlTensorOps
