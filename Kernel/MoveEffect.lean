/-
# `Kernel/MoveEffect.lean` — the derivation engine's first declaration: the kernel `move`

`Effects.EffectSpec` is the generic engine (`EffectSpec → DerivedEffect`, the laws as proof
fields, free by initiality). This file is its first consumer: the kernel's conserving ledger
`move` declared as an effect and derived end-to-end.

`moveEffect`: `Op := MoveArgs` (four scalars — `DecidableEq` + `Repr` + `Countable`, the
N3-clean countable leaf alphabet, the exact opposite of `Signature.OpaqueSig`'s `2^ℵ₀`
payloads), `sem := Kernel.move` (REUSED — the conservation spine). The invocation term
executes (balances computed on `Kernel.k0`, decided), the descriptor is literal data,
conservation (`move_conserves`) rides the derived path unchanged, and the teeth bite.

## Keystone fields (ATLAS law 2), BUILT

* satisfiable — `derive moveEffect` exists and FIRES: the derived executor genuinely
  moves balances on `k0` (decided); the compound program composes; `EffectSpec` is
  premise-inhabited by a real declaration.
* teeth — `ghost_not_derived` (a wrong reading differs from the derived executor,
  witnessed) and `wrong_descriptor_not_effect` (a tampered opcode denotes a different
  transformer).

The declarations keep the namespace `Minidregg.Effects` they were declared in.
-/
import Effects.EffectSpec
import Kernel.State
import Mathlib.Basic.Countable.Basic

namespace Minidregg.Effects

open Minidregg.Compiler Minidregg.Kernel

/-! ## §6. The FIRST declaration — the kernel `move` as an effect. -/

/-- The payload of one `move` invocation — four scalars, SYNTACTIC (comparable,
renderable, countable). The N3-clean leaf alphabet: countable CODES, the exact opposite
of `Theory.Signature.OpaqueSig`'s `2^ℵ₀` function payloads. -/
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
@[reducible] def moveEffect : EffectSpec where
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

/-! ## §9. Axiom pins of the `move` declaration and its teeth (exact output). -/

/-- info: 'Minidregg.Effects.ghost_not_derived' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ghost_not_derived

/-- info: 'Minidregg.Effects.wrong_descriptor_not_effect' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms wrong_descriptor_not_effect

end Minidregg.Effects
