/-
# `Effects/EffectSpec.lean` — the DERIVATION ENGINE's first declaration (ATLAS §7 keystone)

**Substrate, said out loud: this file IS the derived path.** An `EffectSpec` is a
DECLARATION — an operation vocabulary + its executor reading, nothing else. From that one
declaration this file DERIVES (a) the IR term of an invocation, (b) the executor, (c) the
first-order descriptor — all three as folds of `Compiler/Signature`'s initiality engine
(REUSED, never re-derived) — and the laws come FREE: executor-equality by
`agree_by_initiality` (any independent reading is FORCED to coincide — drift impossible by
construction, exactly `Air`'s `eval_agrees_exec`), descriptor-faithfulness by the same
theorem (the descriptor's own first-order reader recovers the executor). Nothing lands
beside what it supersedes: there is no hand-written executor arm, no hand-written
serializer, no per-effect proof anywhere — `derive` is a total function
`EffectSpec → DerivedEffect` whose law fields are discharged once, generically.

## The construction

* `EffectSpec` — the declaration: `Op` (operation payloads — SYNTACTIC data, the N3 law),
  `State`, `sem : Op → State → State` (the declared reading of each op).
* DERIVED IR: `sig` (the effect signature — one leaf `none` = done, one unary node per
  op — the free sequential effect IR), `Prog := Term sig` (mathlib `WType` via
  `Compiler/Signature`), `derivedTerm o` (the invocation term).
* DERIVED executor: `derivedExecutor := fold execAlg`. `execHand` is an INDEPENDENT
  hand-recursion (the adversarial second implementation, the house pattern of `Air`'s
  `evalExec` / `Signature`'s `leafCount` — a witness, not a shipped twin);
  `derived_agrees` forces it equal BY INITIALITY, zero induction at the use site;
  `executor_unique` is the strongest form — EVERY reading that respects the declaration
  per-op IS the derived executor.
* DERIVED descriptor: `derivedDescriptor := fold descAlg : Prog → List Op` — the opcode
  trace, first-order data when `Op` is syntactic; `replay` is the descriptor's OWN reader
  (a first-order list walk over the declaration's op table); `descriptor_faithful`:
  `replay ∘ derivedDescriptor = derivedExecutor` — BY INITIALITY, free.
* THE ENGINE: `derive : (E : EffectSpec) → DerivedEffect E` — the artifact bundle with
  the laws as PROOF FIELDS (the seed of the registry's packed-handler shape). A new
  effect is a DECLARATION; its artifacts and their theorems are a function application.

## The first declaration — the kernel `move` as an effect

`moveEffect`: `Op := MoveArgs` (four scalars — `DecidableEq` + `Repr` + `Countable`, the
N3-clean countable leaf alphabet, the exact opposite of `Signature.OpaqueSig`'s `2^ℵ₀`
payloads), `sem := Kernel.move` (REUSED — the conservation spine). Derived end-to-end:
the invocation term executes (balances computed on `Kernel.k0`, decided), the descriptor
is literal data, conservation (`move_conserves`) rides the derived path unchanged, and
the teeth bite (a ghost reading ≠ the derived executor; a tampered descriptor ≠ the
effect).

## Keystone fields (ATLAS law 2), BUILT

* satisfiable — `derive moveEffect` exists and FIRES: the derived executor genuinely
  moves balances on `k0` (decided); the compound program composes; `EffectSpec` is
  premise-inhabited by a real declaration.
* teeth — `ghost_not_derived` (a wrong reading differs from the derived executor,
  witnessed) and `wrong_descriptor_not_effect` (a tampered opcode denotes a different
  transformer); the agreement is non-vacuous: `execHand` is a genuinely independent
  recursion and both readings compute.

## Boundary

Effects is candidate-side: imports Mathlib + `Compiler.Signature` (the initiality
engine) + `Kernel.State` (the first effect's semantics). `scripts/check-import-boundary.sh`
constrains `Theory`/`Loom` only — it stays green.

Residual: `[EFFECT-registry]` (§8) — the full declaration vocabulary, the open registry,
the weld to the emit path, per-declaration frame/reject teeth, the witness generator.
This lane proves the FIRST declaration derives.
-/
import Compiler.Signature
import Kernel.State
import Mathlib.Data.Countable.Basic

namespace Minidregg.Effects

open Minidregg.Compiler Minidregg.Kernel

/-! ## §1. `EffectSpec` — the declaration. -/

/-- **`EffectSpec`** — ONE effect as ONE declaration: an operation payload type `Op`
(SYNTACTIC data by the N3 law — countable codes, never closures), the state it acts on,
and `sem`, the declared reading of each operation. Everything else in this file is
DERIVED from this record; an author writes nothing beyond it. (The full ATLAS §7
vocabulary — view/touched/guard AST/δ/authority demand, floor obligations as proof
fields — is the `[EFFECT-registry]` residual, §8.) -/
structure EffectSpec : Type 1 where
  /-- Operation payloads — one value per invocable operation, parameters inside.
  SYNTACTIC data (the concrete declaration below is `DecidableEq`+`Repr`+`Countable`):
  opaque `State → _` payloads here would forfeit the faithful descriptor, by
  `Compiler.Signature`'s `[N3-converse]`. -/
  Op : Type
  /-- The state the effect acts on. -/
  State : Type
  /-- The declared semantics — the executor reading of each operation. -/
  sem : Op → State → State

namespace EffectSpec

/-! ## §2. The DERIVED IR — the effect signature and its terms. -/

/-- The DERIVED effect signature: one leaf (`none` — the finished program) and one unary
node per operation (`some o` — perform `o`, then the continuation). An `EffectSpec`'s IR
is not designed, it is this instance of `Compiler.Signature`. -/
def sig (E : EffectSpec) : Signature where
  Op := Option E.Op
  ar := fun s => match s with
    | none => Empty
    | some _ => Unit

/-- **Effect programs** — the free term algebra over the derived signature (mathlib
`WType` through `Compiler.Signature.Term`, REUSED). -/
abbrev Prog (E : EffectSpec) : Type := Term E.sig

/-- The finished program (the `none` leaf). -/
def done (E : EffectSpec) : Prog E := .mk none nofun

/-- Perform `o`, then continue as `p` (the `some o` node). -/
def act (E : EffectSpec) (o : E.Op) (p : Prog E) : Prog E := .mk (some o) fun _ => p

/-- **`derivedTerm` — the IR term of one effect invocation**, derived from the
declaration's payload alone: `act o done`. -/
def derivedTerm (E : EffectSpec) (o : E.Op) : Prog E := E.act o E.done

/-! ## §3. The DERIVED executor — a fold; independent readings FORCED equal. -/

/-- The executor algebra — the declaration's `sem`, per shape: `done ↦ id`,
`act o ↦ (continuation ∘ sem o)`. Choosing this `Alg` IS the whole executor authorship. -/
def execAlg (E : EffectSpec) : Alg E.sig (E.State → E.State) := fun s =>
  match s with
  | none => fun _ => id
  | some o => fun k => k () ∘ E.sem o

/-- **`derivedExecutor` — THE executor, derived**: the fold of `execAlg`. Runs each
operation in program order through the declared `sem`. -/
def derivedExecutor (E : EffectSpec) : Prog E → E.State → E.State := fold E.execAlg

/-- The invocation term executes as the DECLARED semantics — definitionally. -/
@[simp] theorem derivedTerm_exec (E : EffectSpec) (o : E.Op) :
    E.derivedExecutor (E.derivedTerm o) = E.sem o := rfl

/-- Sequencing law, definitional: run `o`, then the rest. -/
@[simp] theorem act_exec (E : EffectSpec) (o : E.Op) (p : Prog E) :
    E.derivedExecutor (E.act o p) = E.derivedExecutor p ∘ E.sem o := rfl

/-- The finished program is the identity — definitionally. -/
@[simp] theorem done_exec (E : EffectSpec) : E.derivedExecutor E.done = id := rfl

/-- An INDEPENDENT hand-recursed executor — written by direct structural recursion, not
via `fold` (the adversarial second implementation; `Air.evalExec`'s pattern). It exists
as the non-vacuity witness for the agreement, never as a shipped twin. -/
def execHand (E : EffectSpec) : Prog E → E.State → E.State
  | .mk none _ => id
  | .mk (some o) k => fun st => execHand E (k ()) (E.sem o st)

/-- The hand-recursion is a fold-homomorphism of `execAlg` — one `rfl` per shape, NO
induction. -/
theorem execHand_isFoldHom (E : EffectSpec) : IsFoldHom E.execAlg E.execHand := by
  intro s k
  cases s <;> rfl

/-- **`derived_agrees` — executor-equality BY INITIALITY.** The independent hand-recursed
executor and the derived fold agree on EVERY program — `agree_by_initiality`, zero
induction at the use site (the one induction was spent once, generically, in
`Compiler.Signature.fold_unique`). Drift between "the spec's executor" and "an
implementation that reads ops the same way" is impossible by construction. -/
theorem derived_agrees (E : EffectSpec) : E.execHand = E.derivedExecutor :=
  agree_by_initiality E.execAlg E.execHand E.derivedExecutor
    E.execHand_isFoldHom (fold_isFoldHom E.execAlg)

/-- The strongest form — `fold_unique` instantiated: EVERY reading that respects the
declaration per-op (`IsFoldHom execAlg`) IS the derived executor. Any future independent
implementation is forced, not audited. -/
theorem executor_unique (E : EffectSpec) (f : Prog E → E.State → E.State)
    (hf : IsFoldHom E.execAlg f) : f = E.derivedExecutor :=
  fold_unique E.execAlg f hf

/-! ## §4. The DERIVED descriptor — first-order data; faithfulness FREE by initiality. -/

/-- The descriptor algebra: serialize a program to its opcode trace. -/
def descAlg (E : EffectSpec) : Alg E.sig (List E.Op) := fun s =>
  match s with
  | none => fun _ => []
  | some o => fun k => o :: k ()

/-- **`derivedDescriptor` — the descriptor, derived**: the fold of `descAlg`. A `List
E.Op` — first-order, serializable data exactly when the declaration's `Op` is syntactic
(the concrete `MoveArgs` below is `DecidableEq`+`Repr`+`Countable`; an opaque `Op` would
hit `[N3-converse]` and could not be read back faithfully). -/
def derivedDescriptor (E : EffectSpec) : Prog E → List E.Op := fold E.descAlg

/-- The invocation's descriptor is its one opcode — definitionally. -/
@[simp] theorem derivedTerm_descriptor (E : EffectSpec) (o : E.Op) :
    E.derivedDescriptor (E.derivedTerm o) = [o] := rfl

/-- Sequencing serializes to `cons` — definitionally. -/
@[simp] theorem act_descriptor (E : EffectSpec) (o : E.Op) (p : Prog E) :
    E.derivedDescriptor (E.act o p) = o :: E.derivedDescriptor p := rfl

/-- **`replay` — the descriptor's OWN reader**: a first-order walk of the opcode list
over the declaration's op table. Mentions no `Term`, no `fold` — a consumer holding only
the descriptor and the op table computes exactly this. -/
def replay (E : EffectSpec) : List E.Op → E.State → E.State
  | [] => id
  | o :: rest => replay E rest ∘ E.sem o

/-- Reading the descriptor back through `replay` is a fold-homomorphism of the EXECUTOR
algebra — one `rfl` per shape. (This is where the descriptor's meaning and the
executor's meaning become two readings of ONE algebra.) -/
theorem replayDescriptor_isFoldHom (E : EffectSpec) :
    IsFoldHom E.execAlg (E.replay ∘ E.derivedDescriptor) := by
  intro s k
  cases s <;> rfl

/-- **`descriptor_faithful` — the descriptor MEANS the effect's semantics, FREE by
initiality.** Replaying the derived descriptor is the derived executor, on EVERY
program — `agree_by_initiality` on `execAlg`, zero induction at the use site. The
serialized artifact and the semantics cannot drift: they are the same fold. -/
theorem descriptor_faithful (E : EffectSpec) :
    E.replay ∘ E.derivedDescriptor = E.derivedExecutor :=
  agree_by_initiality E.execAlg (E.replay ∘ E.derivedDescriptor) E.derivedExecutor
    E.replayDescriptor_isFoldHom (fold_isFoldHom E.execAlg)

/-- Pointwise form — the shape a consumer uses on one program. -/
theorem descriptor_faithful_apply (E : EffectSpec) (p : Prog E) :
    E.replay (E.derivedDescriptor p) = E.derivedExecutor p :=
  congrFun (descriptor_faithful E) p

end EffectSpec

/-! ## §5. THE ENGINE — `EffectSpec → DerivedEffect`, laws as proof fields.

The derived-path claim, stated as one total function: EVERY declaration yields its
term/executor/descriptor bundle with executor-uniqueness and descriptor-faithfulness
already discharged — a new effect is a DECLARATION, not hand-authored code. The bundle's
proof-field shape is deliberately the seed of the registry's packed handler (ATLAS §4:
ALL floor obligations as proof fields, "not 3 of 9 typed and 6 as side-hypotheses"). -/

/-- The derived artifact bundle of one declaration — artifacts + their laws as PROOF
FIELDS (ill-typed until discharged; `derive` discharges them generically, once). -/
structure DerivedEffect (E : EffectSpec) where
  /-- The IR term of an invocation. -/
  term : E.Op → EffectSpec.Prog E
  /-- The executor. -/
  exec : EffectSpec.Prog E → E.State → E.State
  /-- The first-order descriptor. -/
  descriptor : EffectSpec.Prog E → List E.Op
  /-- The invocation term executes as the declared semantics. -/
  term_exec : ∀ o, exec (term o) = E.sem o
  /-- Executor-uniqueness: every per-op-respecting reading IS `exec` (drift-free). -/
  exec_unique : ∀ f, IsFoldHom E.execAlg f → f = exec
  /-- The descriptor read back through `replay` IS `exec` (faithful serialization). -/
  descriptor_faithful : E.replay ∘ descriptor = exec

/-- **`derive` — THE DERIVATION ENGINE, first rung.** Total, hypothesis-free: every
`EffectSpec` yields its `DerivedEffect` by `fold` + initiality — no per-effect proof, no
hand-authored artifact, anywhere. This function application is what "the derived path is
the ONLY path" means for effects. -/
def derive (E : EffectSpec) : DerivedEffect E where
  term := E.derivedTerm
  exec := E.derivedExecutor
  descriptor := E.derivedDescriptor
  term_exec := E.derivedTerm_exec
  exec_unique := E.executor_unique
  descriptor_faithful := E.descriptor_faithful

/-! ## §6. The FIRST declaration — the kernel `move` as an effect. -/

/-- The payload of one `move` invocation — four scalars, SYNTACTIC (comparable,
renderable, countable). The N3-clean leaf alphabet: countable CODES, the exact opposite
of `Compiler.Signature.OpaqueSig`'s `2^ℵ₀` function payloads. -/
structure MoveArgs where
  src : CellId
  dst : CellId
  asset : AssetId
  δ : ℤ
  deriving DecidableEq, Repr

/-- `MoveArgs` is countable — the descriptor alphabet is genuinely syntax (the
`[N3-converse]` requirement on leaves, exhibited, not asserted). -/
instance : Countable MoveArgs :=
  have h : Function.Injective (fun m : MoveArgs => (m.src, m.dst, m.asset, m.δ)) := by
    intro a b hab
    cases a; cases b; simpa using hab
  h.countable

/-- **The first real declaration** — the kernel's conserving ledger `move`
(`Kernel.State.move`, REUSED — the conservation spine) as an effect. This record is the
ENTIRE authored surface; term, executor, descriptor, and their laws are `derive`d. -/
def moveEffect : EffectSpec where
  Op := MoveArgs
  State := KernelState
  sem := fun m k => move k m.src m.dst m.asset m.δ

/-- The derived IR term of one invocation: move 2 of asset 0 from cell 0 to cell 1. -/
def moveTerm : EffectSpec.Prog moveEffect := moveEffect.derivedTerm ⟨0, 1, 0, 2⟩

/-- A COMPOUND derived program: move 2 (0→1), then move 1 back (1→0). -/
def moveProg : EffectSpec.Prog moveEffect :=
  moveEffect.act ⟨0, 1, 0, 2⟩ (moveEffect.derivedTerm ⟨1, 0, 0, 1⟩)

/-! ## §7. Keystone witnesses — the first effect DERIVES, FIRES, and BITES (on `k0`).

`Kernel.k0` (REUSED): cells `{0, 1}` holding 5 and 3 of asset 0. Everything below is
decided/computed against that literal state. -/

/-- *Satisfiable / the engine fires*: the DERIVED executor of the DERIVED invocation term
genuinely moves the ledger — cell 0 debited 5 → 3 … -/
example : ((derive moveEffect).exec moveTerm k0).bal 0 0 = 3 := by decide

/-- … cell 1 credited 3 → 5. The bundle's executor computes; the declaration ran. -/
example : ((derive moveEffect).exec moveTerm k0).bal 1 0 = 5 := by decide

/-- *Sequencing fires*: the compound program composes through the derived executor
(5−2+1 = 4 and 3+2−1 = 4). -/
example : (moveEffect.derivedExecutor moveProg k0).bal 0 0 = 4 ∧
    (moveEffect.derivedExecutor moveProg k0).bal 1 0 = 4 := by
  exact ⟨by decide, by decide⟩

/-- *The agreement is about two readings that BOTH compute*: the independent
hand-recursion reaches the same state — and not by coincidence, by `derived_agrees`. -/
example : (moveEffect.execHand moveProg k0).bal 1 0 = 4 := by decide

/-- *`derived_agrees` fires on the concrete effect*: the two readings coincide on the
compound program — instantiated, not re-proved. -/
example : moveEffect.execHand moveProg k0 = moveEffect.derivedExecutor moveProg k0 :=
  congrFun (congrFun (EffectSpec.derived_agrees moveEffect) moveProg) k0

/-- *Initiality PINS compound programs*: ANY per-op-respecting reading is forced to the
derived value on `moveProg` — the collapse bites on non-atomic terms (the genuine content
of `fold_unique`), zero induction here. -/
example (f : EffectSpec.Prog moveEffect → KernelState → KernelState)
    (hf : IsFoldHom moveEffect.execAlg f) : (f moveProg k0).bal 0 0 = 4 := by
  rw [moveEffect.executor_unique f hf]
  decide

/-- *The kernel CONTRACT rides the derived path*: the derived invocation conserves the
per-asset total — `move_conserves` (REUSED) applies verbatim because the derived
executor of the derived term IS the kernel `move`, definitionally. Inherited, not
re-proved — the factory-cell promise at n = 1. -/
example : totalAsset (moveEffect.derivedExecutor moveTerm k0) 0 = totalAsset k0 0 := by
  have h : moveEffect.derivedExecutor moveTerm k0 = move k0 0 1 0 2 := rfl
  rw [h]
  exact move_conserves k0 0 1 0 2 (by decide) (by decide)

/-- *The descriptor is LITERAL first-order data*: the invocation serializes to its one
opcode record; the compound program to its trace. Comparable (`DecidableEq`), renderable
(`Repr`), countable — a consumer needs no Lean function to hold it. -/
example : moveEffect.derivedDescriptor moveTerm = [⟨0, 1, 0, 2⟩] := rfl

example : moveEffect.derivedDescriptor moveProg = [⟨0, 1, 0, 2⟩, ⟨1, 0, 0, 1⟩] := rfl

/-- *Faithfulness fires on the concrete effect*: replaying the derived descriptor IS the
derived executor on the compound program — `descriptor_faithful` instantiated. -/
example : moveEffect.replay (moveEffect.derivedDescriptor moveProg)
    = moveEffect.derivedExecutor moveProg :=
  EffectSpec.descriptor_faithful_apply moveEffect moveProg

/-- The WRONG reading — a fail-open "executor" that drops every operation. -/
def ghostAlg : Alg moveEffect.sig (KernelState → KernelState) := fun _ _ => id

/-- **Executor TEETH**: the ghost reading is NOT the derived executor — witnessed on the
invocation at `k0` (cell 1 reads 3 under the ghost, 5 under the derived path). The
agreement theorems are non-vacuous: a reading that mis-reads an op genuinely differs,
and (by `executor_unique`'s contrapositive) the ghost is no fold-homomorphism of the
declaration. -/
theorem ghost_not_derived : fold ghostAlg ≠ moveEffect.derivedExecutor := fun h =>
  absurd (congrArg (fun g => (g moveTerm k0).bal 1 0) h) (by decide)

/-- **Descriptor TEETH**: a TAMPERED descriptor is not a rendering of the effect —
altering the opcode's δ (3 for 2) replays to a DIFFERENT transformer than the derived
executor (cell 1: 6 ≠ 5 at `k0`). The descriptor's content is load-bearing, not a label. -/
theorem wrong_descriptor_not_effect :
    moveEffect.replay [⟨0, 1, 0, 3⟩] ≠ moveEffect.derivedExecutor moveTerm := fun h =>
  absurd (congrArg (fun g => (g k0).bal 1 0) h) (by decide)

/-- …and the tampered descriptor is DISTINGUISHABLE as data (`DecidableEq`, decided) —
wrong bytes are caught before replay ever runs. -/
example : ([⟨0, 1, 0, 3⟩] : List MoveArgs) ≠ moveEffect.derivedDescriptor moveTerm := by
  decide

/-! ## §8. `[EFFECT-registry]` — the residual (named, not stubbed).

This file proves the ENGINE at its first declaration. The OPEN REGISTRY it seeds — the
rest of ATLAS §7's Effects carve — is:

* the FULL declaration vocabulary: view, touched footprint, leaf exprs, guard AST (from
  `Pred` — with REJECTION: `sem` here is total; the gated form is the 4-leg gate's
  effect face), δ, authority demand — with ALL floor obligations as PROOF FIELDS on the
  declaration (`DerivedEffect` is the seed shape: its laws already ride as fields);
* the registry itself: an open list of packed handlers + the dispatch executor, every
  entry a `derive`d bundle — never "3 of 9 typed and 6 as side-hypotheses";
* the WELD to the emit path: the effect's guard/δ bound into `Compiler`'s
  `ConstraintDescriptor` (law 12 — bind the policy TERM, not the decision bit), so a
  receipt proves the policy held, not "the executor said admit";
* per-declaration frame/reject teeth and the witness GENERATOR (RED/GREEN non-vacuity
  witnesses demanded from the author, generated for the shared shape).

Honest scope of THIS file's descriptor: `derivedDescriptor` + `replay` serialize and
faithfully read back the effect PROGRAM (the opcode trace) — `replay` recovers the FULL
transformer semantics from first-order data given the declaration's op table. Compiling
the ops' SEMANTICS themselves into constraints (the AIR statement of a move) is the weld
above; it is not claimed here. -/

/-! ## §9. Axiom pins — exact-output, self-verifying (the build fails on drift).

The engine theorems ride `fold_unique`'s one induction (`funext` ⇒ `Quot.sound`); the
teeth are `decide`-computed. Kernel-clean throughout — the exact footprint is
`[Quot.sound]`, strictly inside the `{propext, Classical.choice, Quot.sound}` ceiling. -/

/-- info: 'Minidregg.Effects.EffectSpec.derived_agrees' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms EffectSpec.derived_agrees

/-- info: 'Minidregg.Effects.EffectSpec.descriptor_faithful' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms EffectSpec.descriptor_faithful

/-- info: 'Minidregg.Effects.EffectSpec.executor_unique' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms EffectSpec.executor_unique

/-- info: 'Minidregg.Effects.derive' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms derive

/-- info: 'Minidregg.Effects.ghost_not_derived' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ghost_not_derived

/-- info: 'Minidregg.Effects.wrong_descriptor_not_effect' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms wrong_descriptor_not_effect

end Minidregg.Effects
