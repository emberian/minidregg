/-
# `Theory/EvmResidual.lean` — the Stage-0 residual vocabulary, and the UNTRUSTED decompiler

The middle of the Stage-0 chain (`zkml-research/notes/evm-decompilation.md` §5–§6):

```
  evmRun fragmentCode          (Theory/EvmFragment: the machine — stack, PC, decode)
    ⇣  decompile                (HERE, untrusted: a refusing symbolic stack machine)
  fragmentResidual              (the residual term: 2 calldata-word context roles + one add)
    ⇣  fragment_faithful        (HERE: the per-output translation-validation theorem)
  Residual.denote               (the residual's total denotation)
```

## The decompilation is VISIBLE, and the decompiler is UNTRUSTED

`decompile` is an executable symbolic stack machine over the same bytes the real
machine runs: PUSH1 produces a `lit`, CALLDATALOAD at a `lit` offset produces a
`cdw`, ADD produces an `addw` node, MSTORE records a static-offset write, RETURN
demands exactly one write at exactly the returned offset and 32 returned bytes.
Everything else — a data-dependent offset, STOP, any opcode outside the
fragment, any memory shape Stage 0 cannot prove — is REFUSED, never repaired
(`ZkmlTraceCheck`'s posture). NO theorem quantifies over `decompile`'s inputs:
the decompiler carries no trust. What carries the trust is the PER-OUTPUT pair

* `decompile_fragment : decompile fragmentCode = .ok fragmentResidual` — the
  decompilation, exhibited (kernel-computed, `rfl`);
* `fragment_faithful : ∀ cd, evmRun fragmentCode cd = .ok (beBytes
  (fragmentResidual.denote cd))` — translation validation for THIS output,
  quantified over ALL calldata. Genuine TV: both sides live in Lean.

This is the design note's §1.4 stance executed: not the second Futamura
projection (a verified decompiler), but per-output TV — the decompiler free to
be heuristic, each output carrying its own machine-checked refinement.

## What died, visibly

`fragmentResidual` is `{cd[32], cd[0]} ⊢ add(w0, w1)`. The 15-byte program's
PC, its fetch/decode, all five PUSH1s, the stack discipline, the MSTORE and the
RETURN byte-shuffling appear NOWHERE in it — the machine died in specialization,
and `fragment_faithful` is the proof the death was faithful. The context entries
carry ROLES (`cdWordAt 32`, `cdWordAt 0` — which calldata word entered which
wire), the `[N3-converse]` discipline: a residual that cannot name its inputs
cannot be checked against the transaction.

## Stage-0 scope, stated

The vocabulary has exactly the constructors this fragment's chain proves end to
end: calldata-word context roles and `add`. Nothing unused is declared — one op
with a complete path beats twenty with none; Stage 1 grows {cmp, iszero,
select, guard, shiftConst, bit} WITH their emit path, not before it. Duplicate
calldata offsets are not deduplicated (a duplicate costs a context wire, never
soundness). The straight-line fuel is `code.length + 1`: no jumps in Stage 0.
-/
import Mathlib.Tactic
import Theory.EvmFragment

namespace Minidregg.Theory.EvmResidual

open Minidregg.Theory.EvmFragment

set_option autoImplicit false

/-! ## §1. The residual vocabulary — context roles, intrinsically scoped expressions. -/

/-- A context entry names WHERE its value enters from — the role discipline.
Stage 0 has one role: a 32-byte calldata read at a STATIC offset. -/
inductive CtxEntry
  | cdWordAt (offset : ℕ)
  deriving DecidableEq, Repr

/-- Residual expressions over `n` context wires. `Fin n` scoping makes an
out-of-scope wire UNREPRESENTABLE — intrinsic well-scopedness, the
`ZkmlTraceCheck` property at Stage-0 scale. `add` is the u256 add; wraparound
at `2^256` IS the semantics. -/
inductive RExpr (n : ℕ)
  | wire (i : Fin n)
  | add (a b : RExpr n)
  deriving Repr

/-- A residual program: named-role context, one scoped expression, whose value
is the single returned word. -/
structure Residual where
  ctx : List CtxEntry
  body : RExpr ctx.length

/-- What a context entry denotes, given the transaction's calldata. -/
def CtxEntry.denote (cd : List ℕ) : CtxEntry → ℕ
  | .cdWordAt off => cdWord cd off

/-- The residual expression's total denotation. -/
def RExpr.denote {n : ℕ} (env : Fin n → ℕ) : RExpr n → ℕ
  | .wire i => env i
  | .add a b => (RExpr.denote env a + RExpr.denote env b) % wordMod

/-- **The residual's denotation**: the returned word, as a function of calldata. -/
def Residual.denote (D : Residual) (cd : List ℕ) : ℕ :=
  D.body.denote fun i => (D.ctx.get i).denote cd

/-! ## §2. The decompiler — an executable, refusing symbolic stack machine. -/

/-- Symbolic words: a PUSH-ed machine constant, a calldata word at a static
offset, or a u256 add of two symbolic words. -/
inductive SymWord
  | lit (v : ℕ)
  | cdw (offset : ℕ)
  | addw (a b : SymWord)
  deriving DecidableEq, Repr

/-- The context a symbolic word needs, in operand order (left to right). -/
def SymWord.ctxEntries : SymWord → List CtxEntry
  | .lit _ => []
  | .cdw o => [CtxEntry.cdWordAt o]
  | .addw a b => a.ctxEntries ++ b.ctxEntries

/-- First index of `a` in `l`, with its bound — the de Bruijn resolver. -/
def findFin {α : Type} [DecidableEq α] (a : α) : (l : List α) → Option (Fin l.length)
  | [] => none
  | x :: xs =>
      if x = a then some ⟨0, by simp⟩
      else (findFin a xs).map fun i => ⟨i.1 + 1, by simp only [List.length_cons]; omega⟩

/-- Lower a symbolic word to a scoped residual expression over a context.
A machine constant reaching the returned word is REFUSED in Stage 0 (nothing in
this vocabulary carries it — that is Stage 1's `literal` role). -/
def SymWord.toRExpr (ctx : List CtxEntry) : SymWord → Except String (RExpr ctx.length)
  | .lit _ => .error "Stage 0: a PUSH constant flowed into the returned word"
  | .cdw o =>
      match findFin (CtxEntry.cdWordAt o) ctx with
      | some i => .ok (.wire i)
      | none => .error "internal: calldata offset missing from its own context"
  | .addw a b => do
      let ra ← SymWord.toRExpr ctx a
      let rb ← SymWord.toRExpr ctx b
      .ok (.add ra rb)

/-- Symbolic machine state: `pc`, symbolic stack, the static-offset MSTORE log
(most recent first). -/
structure SymState where
  pc : ℕ
  stack : List SymWord
  writes : List (ℕ × SymWord)

/-- A symbolic step's outcome. -/
inductive SymStep
  | cont (s : SymState)
  | ret (D : Residual)
  | refuse (msg : String)

/-- **One symbolic step.** The dispatch mirrors `EvmFragment.step` byte for
byte; every shape Stage 0 cannot lower is a refusal with its reason. -/
def decompileStep (code : List ℕ) (s : SymState) : SymStep :=
  match code.getD s.pc 0 with
  | 0x00 => .refuse "Stage 0: STOP — no returned word to decompile"
  | 0x01 =>
      match s.stack with
      | a :: b :: rest => .cont ⟨s.pc + 1, .addw a b :: rest, s.writes⟩
      | _ => .refuse "ADD: stack underflow"
  | 0x35 =>
      match s.stack with
      | .lit o :: rest => .cont ⟨s.pc + 1, .cdw o :: rest, s.writes⟩
      | _ :: _ => .refuse "Stage 0: CALLDATALOAD at a data-dependent offset"
      | _ => .refuse "CALLDATALOAD: stack underflow"
  | 0x52 =>
      match s.stack with
      | .lit o :: v :: rest => .cont ⟨s.pc + 1, rest, (o, v) :: s.writes⟩
      | _ :: _ :: _ => .refuse "Stage 0: MSTORE at a data-dependent offset"
      | _ => .refuse "MSTORE: stack underflow"
  | 0x60 => .cont ⟨s.pc + 2, .lit (code.getD (s.pc + 1) 0) :: s.stack, s.writes⟩
  | 0xf3 =>
      match s.stack with
      | .lit o :: .lit 32 :: _ =>
          match s.writes with
          | [(o', w)] =>
              if o' = o then
                match SymWord.toRExpr w.ctxEntries w with
                | .ok body => .ret ⟨w.ctxEntries, body⟩
                | .error e => .refuse e
              else .refuse "Stage 0: RETURN offset differs from the single MSTORE"
          | _ => .refuse "Stage 0: memory shape (exactly one MSTORE required)"
      | _ :: _ :: _ => .refuse "Stage 0: RETURN needs a constant offset and length 32"
      | _ => .refuse "RETURN: stack underflow"
  | _ => .refuse "opcode outside the Stage-0 fragment"

/-- The fueled symbolic driver. -/
def decompileRun (code : List ℕ) : ℕ → SymState → Except String Residual
  | 0, _ => .error "decompile: out of fuel"
  | fuel + 1, s =>
      match decompileStep code s with
      | .cont s' => decompileRun code fuel s'
      | .ret D => .ok D
      | .refuse m => .error m

/-- **The decompiler.** UNTRUSTED and partial by design: its only obligations
are the per-output pairs below. Straight-line fuel `code.length + 1`. -/
def decompile (code : List ℕ) : Except String Residual :=
  decompileRun code (code.length + 1) ⟨0, [], []⟩

/-! ## §3. The Stage-0 output pair: the decompilation EXHIBITED, then VALIDATED. -/

/-- The fragment's residual: context `{cd[32], cd[0]}` (operand order — the EVM
stack popped the offset-32 word first), body `add(w0, w1)`. The machine is GONE. -/
def fragmentResidual : Residual :=
  ⟨[.cdWordAt 32, .cdWordAt 0], .add (.wire 0) (.wire 1)⟩

/-- **The decompilation, exhibited**: running the decompiler on the 15 bytes
produces exactly `fragmentResidual` — kernel-computed, not asserted. -/
theorem decompile_fragment : decompile fragmentCode = .ok fragmentResidual := rfl

/-- **`fragment_faithful` — per-output translation validation, the Stage-0
keystone.** For EVERY calldata, the byte-level machine run of the 15-byte
program returns exactly the 32 big-endian bytes of the residual's denotation.
The proof is `rfl`: with the program concrete and the calldata symbolic, the
machine's stack, PC, fetch/decode, MSTORE and RETURN all REDUCE AWAY, and what
is left is definitionally the residual. That reduction is the decompilation
theorem — the specialized-away machine was pure structure.

Scope premise (design note §7.5): `evmRun` is gas-free — this speaks about
executions the deployed EVM completes within gas. -/
theorem fragment_faithful (cd : List ℕ) :
    evmRun fragmentFuel fragmentCode cd
      = .ok (beBytes (fragmentResidual.denote cd)) := rfl

/-! ## §4. Teeth. The refusals refuse, and the TV obligation discriminates. -/

/-- *Refusal, computed*: STOP has no returned word — refused, not defaulted. -/
theorem decompile_refuses_stop :
    decompile [0x00] = .error "Stage 0: STOP — no returned word to decompile" := rfl

/-- *Refusal, computed*: a CALLDATALOAD whose offset is itself loaded from
calldata (data-dependent addressing) is refused — the §7.1 doctrine at the
smallest scale. -/
theorem decompile_refuses_dynamic_offset :
    decompile [0x60, 0x00, 0x35, 0x35]
      = .error "Stage 0: CALLDATALOAD at a data-dependent offset" := rfl

/-- *Refusal, computed*: an opcode outside the fragment (MUL, `0x02`). -/
theorem decompile_refuses_foreign_opcode :
    decompile [0x60, 0x01, 0x60, 0x02, 0x02]
      = .error "opcode outside the Stage-0 fragment" := rfl

/-- A WRONG residual for the fragment — same shape, operands both wire 1
(i.e. `cd[0] + cd[0]` instead of `cd[32] + cd[0]`). -/
def fragmentResidualForged : Residual :=
  ⟨[.cdWordAt 32, .cdWordAt 0], .add (.wire 1) (.wire 1)⟩

/-- *The mutation is real*: on V1's calldata the forged residual denotes `2`
where the true one denotes `3` — asserted BEFORE the refusal is read. -/
theorem forged_residual_differs :
    fragmentResidualForged.denote (calldataOf 1 2) = 2
      ∧ fragmentResidual.denote (calldataOf 1 2) = 3 := by decide

/-- *TV has teeth, computed*: the machine run REFUTES the forged residual on
V1's calldata — the translation-validation obligation genuinely discriminates
between residuals; it is not satisfied by shape. -/
theorem forged_residual_fails_tv :
    ¬ (evmRun fragmentFuel fragmentCode (calldataOf 1 2)
        = .ok (beBytes (fragmentResidualForged.denote (calldataOf 1 2)))) := by
  decide

/-! ## §5. Axiom accounting. (The `rfl` proofs are kernel computation; the
axioms recorded are those of the DEFINITIONS the statements mention — e.g.
`findFin`'s `Fin` bound proofs — not of any reasoning step.) -/

/-- info: 'Minidregg.Theory.EvmResidual.decompile_fragment' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decompile_fragment

/-- info: 'Minidregg.Theory.EvmResidual.fragment_faithful' depends on axioms:
[propext] -/
#guard_msgs (whitespace := lax) in #print axioms fragment_faithful

/-- info: 'Minidregg.Theory.EvmResidual.forged_residual_fails_tv' depends on axioms:
[propext] -/
#guard_msgs (whitespace := lax) in #print axioms forged_residual_fails_tv

end Minidregg.Theory.EvmResidual
