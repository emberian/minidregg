/-
# `Compiler/Air.lean` — the arithmetization DSL, DERIVED (the constraint reading is a fold)

The private-witness turn HIDES (`Assurance/PrivateTurn`) but does not yet SOUNDLY CONSTRAIN:
that needs an arithmetization — the note-opening / nullifier / membership relations as
CONSTRAINTS. **The derived-path law (and the AIR-in-Lean tripwire): constraints are NOT
hand-authored — they come out of the compiler, or the compiler grows the vocabulary.** This
file is the first rung: an arithmetization DSL as a `Compiler.Signature`, its executor reading
and its circuit reading BOTH as folds of one algebra, so `circuit ⟺ executor` is FREE by
initiality (`agree_by_initiality`, N3) — drift is not "avoided", it is impossible by
construction. breadstuffs' Rust AIRs (`*_air.rs`) are the DEBT this replaces; nothing is ported.

**Substrate, said out loud:** this is Lean-authored arithmetization. An expression term is a
`Term AirSig`; the CIRCUIT evaluation is `fold evalAlg`; the EXECUTOR is an independent
hand-recursion; `eval_agrees_exec` proves them equal on EVERY term by initiality, with zero
induction at the use site. A constraint "the emitted circuit accepts the assignment" is, by that
theorem, exactly "the executor's relation holds" — the arithmetization means what the semantics
say, not by audit but by the one induction spent once in `Compiler/Signature.fold_unique`.

N3 respected: `AirOp`'s payloads are SYNTACTIC (a field element `c : F`, a variable index) —
countable, not opaque `σ → Bool` closures — so the second (circuit) reading is faithful, exactly
the `[N3-converse]` law's requirement.

Honestly scoped (residuals, none stubbed): `[AIR-flatten]` — flattening a nested expression to a
degree-≤2 constraint SYSTEM with aux wires (R1CS/Plonkish gates) and proving the flattening
preserves semantics; `[AIR-sumcheck]` — retiring the emitted polynomial constraint through
`Loom/SumcheckReduction`; `[AIR-poseidon]`/`[AIR-membership]` — the hash + Merkle gadgets that
make a note-spend, grown on this rung. This file proves the RUNG (a DSL whose constraint reading
is a drift-free fold + a first gadget), not the note-spend.
-/
import Compiler.Signature
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

namespace Minidregg.Compiler

universe u

variable {F : Type u} [Field F] {Idx : Type u}

/-! ## §1. The arithmetization signature — arithmetic expressions over `F`, `Idx`-indexed. -/

/-- Operation shapes of the arithmetization DSL: a constant `const c` and a variable
`var i` (leaves, their payloads SYNTACTIC — a field element / an index, countable, N3-clean),
and the binary gates `add`/`mul`. -/
inductive AirOp (F : Type u) (Idx : Type u)
  | const (c : F)
  | var (i : Idx)
  | add
  | mul

/-- The arithmetization signature: `const`/`var` are leaves (empty arity), `add`/`mul` are
binary (`Bool`-indexed), matching `Compiler/Signature`'s container convention. -/
def AirSig (F : Type u) (Idx : Type u) : Signature where
  Op := AirOp F Idx
  ar := fun s => match s with
    | .const _ | .var _ => Empty
    | .add | .mul => Bool

/-- Expression constructors — the DSL surface syntax. -/
def cst (c : F) : Term (AirSig F Idx) := .mk (.const c) nofun
def vr (i : Idx) : Term (AirSig F Idx) := .mk (.var i) nofun
def add' (a b : Term (AirSig F Idx)) : Term (AirSig F Idx) := .mk .add fun t => bif t then b else a
def mul' (a b : Term (AirSig F Idx)) : Term (AirSig F Idx) := .mk .mul fun t => bif t then b else a

/-! ## §2. Two readings of the same algebra — the CIRCUIT eval (a fold) and the EXECUTOR. -/

/-- The evaluation algebra at an assignment `asg`: `const c ↦ c`, `var i ↦ asg i`,
`add ↦ (+)`, `mul ↦ (*)`. Choosing this `Alg` IS choosing how the circuit reads each primitive. -/
def evalAlg (asg : Idx → F) : Alg (AirSig F Idx) F := fun s =>
  match s with
  | .const c => fun _ => c
  | .var i => fun _ => asg i
  | .add => fun k => k false + k true
  | .mul => fun k => k false * k true

/-- **The CIRCUIT reading** — evaluate an expression by folding `evalAlg`. -/
def eval (asg : Idx → F) : Term (AirSig F Idx) → F := fold (evalAlg asg)

/-- **The EXECUTOR reading** — an INDEPENDENT hand-recursion (the "semantics", written without
`fold`, the way a separate implementation would). -/
def evalExec (asg : Idx → F) : Term (AirSig F Idx) → F
  | .mk (.const c) _ => c
  | .mk (.var i) _ => asg i
  | .mk .add k => evalExec asg (k false) + evalExec asg (k true)
  | .mk .mul k => evalExec asg (k false) * evalExec asg (k true)

/-- The executor is a fold-homomorphism of `evalAlg` — one `rfl` per shape, NO induction. -/
theorem evalExec_isFoldHom (asg : Idx → F) : IsFoldHom (evalAlg asg) (evalExec asg) := by
  intro s k
  cases s <;> rfl

/-- **`eval_agrees_exec` — CIRCUIT ⟺ EXECUTOR, FREE BY INITIALITY.** The circuit evaluation and
the independent executor agree on EVERY expression, by `agree_by_initiality` — zero induction at
the use site (the one induction was spent once, generically, in `fold_unique`). This is the
N3 drift-impossibility for arithmetization: the two readings CANNOT disagree. -/
theorem eval_agrees_exec (asg : Idx → F) : evalExec asg = eval asg (F := F) (Idx := Idx) :=
  agree_by_initiality (evalAlg asg) (evalExec asg) (eval asg)
    (evalExec_isFoldHom asg) (fold_isFoldHom (evalAlg asg))

/-! ## §3. Constraints — "the circuit accepts `asg`" is "the executor's relation holds".

An assertion `t = 0` becomes the constraint predicate `accepts`. Because the circuit eval and the
executor coincide (§2), the circuit's acceptance is DEFINED by the executor's semantics — the
arithmetization means what it computes. This is the derived-path refinement at the expression
level; `[AIR-flatten]` lifts it to a gate SYSTEM. -/

/-- The CIRCUIT constraint: the assignment satisfies the assertion `t = 0` under the circuit
reading. -/
def accepts (asg : Idx → F) (t : Term (AirSig F Idx)) : Prop := eval asg t = 0

/-- The EXECUTOR relation: the assertion holds under the semantics. -/
def semHolds (asg : Idx → F) (t : Term (AirSig F Idx)) : Prop := evalExec asg t = 0

/-- **The refinement keystone — the circuit constraint ⟺ the executor relation.** By initiality,
"the emitted circuit accepts `asg`" is EXACTLY "the executor's relation holds" — the drift-free
arithmetization contract, proved for every expression with no per-gadget induction. -/
theorem accepts_iff_semHolds (asg : Idx → F) (t : Term (AirSig F Idx)) :
    accepts asg t ↔ semHolds asg t := by
  unfold accepts semHolds
  rw [eval_agrees_exec]

/-! ## §4. First gadget — booleanity `x·(x−1) = 0`, DERIVED through the DSL.

The simplest AIR gate: a wire is boolean iff `x² − x = 0`. Built as a DSL term, its constraint
meaning proved via the refinement — the pattern every later gadget (range, hash, membership)
follows. -/

/-- The booleanity assertion for variable `i`: `vr i * (vr i - cst 1)`, i.e. `x·(x−1)`. -/
def boolGadget (i : Idx) : Term (AirSig F Idx) :=
  mul' (vr i) (add' (vr i) (cst (-1)))

/-- **The booleanity gadget MEANS booleanity**: the circuit accepts `asg` iff `asg i ∈ {0,1}`.
Derived — the constraint's semantics fall straight out of `accepts_iff_semHolds` + the executor
computation, no bespoke soundness argument. -/
theorem boolGadget_correct (asg : Idx → F) (i : Idx) :
    accepts asg (boolGadget i) ↔ (asg i = 0 ∨ asg i = 1) := by
  rw [accepts_iff_semHolds]
  show asg i * (asg i + (-1)) = 0 ↔ _
  rw [mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero]

/-! ### Keystone witnesses — the DSL computes and the gadget bites (ZMod 7, a finite field). -/

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- *Satisfiable / computes*: `(x + 2)·x` at `x = 3` over `ZMod 7` = `15 = 1` — the eval runs. -/
example : eval (fun _ : Unit => (3 : ZMod 7)) (mul' (add' (vr ()) (cst 2)) (vr ())) = 1 := by
  decide

/-- *The circuit and executor agree, computed*: both readings coincide on the same expression. -/
example : evalExec (fun _ : Unit => (3 : ZMod 7)) (mul' (add' (vr ()) (cst 2)) (vr ()))
    = eval (fun _ : Unit => (3 : ZMod 7)) (mul' (add' (vr ()) (cst 2)) (vr ())) := by
  rw [eval_agrees_exec]

/-- *Gadget satisfiable*: booleanity accepts `x = 1`. -/
example : accepts (fun _ : Unit => (1 : ZMod 7)) (boolGadget ()) := by
  rw [boolGadget_correct]; exact Or.inr rfl

/-- *Gadget teeth*: booleanity REJECTS `x = 2` (a non-boolean) — the constraint genuinely
constrains. -/
example : ¬ accepts (fun _ : Unit => (2 : ZMod 7)) (boolGadget ()) := by
  rw [boolGadget_correct]; decide

/-! ### Honest residuals — the rungs above this one (Lean-authored, none stubbed)

`[AIR-flatten]` — a nested expression compiles to a degree-≤2 constraint SYSTEM with aux wires
(each `mul`/`add` a gate, aux variables forced to intermediates); the refinement is that the
flattened system is satisfiable iff the expression evaluates to its target. This is the real
arithmetization (this file asserts one polynomial `= 0`; deployment needs bounded-degree gates).
Derived the same way — the flattening is a fold into a gate list, its soundness a fold-hom.

`[AIR-sumcheck]` — the emitted polynomial/gate constraint is RETIRED by `Loom/SumcheckReduction`
(a constraint IS a sumcheck claim). Wires this DSL to the proven proof system.

`[AIR-poseidon]` / `[AIR-membership]` — the Poseidon2 hash gate and the Merkle-membership circuit
(the note-spend's real constraints, `shielded_exact_apex_v4` as design reference), grown as DSL
subterms on this rung. These make the private-witness turn SOUNDLY CONSTRAIN — the [PRIVATE-TURN-air]
residual — and they are the arithmetization compiler's real mass, authored here, never ported.
-/

end Minidregg.Compiler
