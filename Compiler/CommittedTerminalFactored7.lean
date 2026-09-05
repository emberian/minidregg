/-
# Compiler.CommittedTerminalFactored7 -- the receipt's seven factored terminals, realized

`Compiler/Ext6GateProofController.lean:222` carries `terminalValue : Fin 7 -> Ext6Q`
-- the seven factored terminals of `GateFactoredExt6` in `terminalOrder`
(`mulA, mulB, mulC, addA, addB, addC, zero`) -- and `Accepts` (`:323`) takes
them on faith: it checks that the quadratic chain closes at
`terminalExpression receipt.terminalValue`, but nothing in the tree produces
the seven values from a committed trace.  `GateFactoredExt6.lean:550
TerminalOpenings` is the interface a commitment layer must inhabit for them;
its only inhabitant is the proof-side `Ext6GateProofPositiveRun.honestOpenings`
(`rfl` at a `Classical.choose`d trace).

This module realizes the seven from the opened word at full-word resolution,
exactly as `CommittedTerminalRealizer` realizes the single terminal:

* **One generic lane walker.**  `walk` folds a list with a running gamma
  power and a per-position corner weight, materializing every lane product
  (`Ext6L`, strict -- the realizer's §5 lesson); `read_walk` is its one
  bridge into the proved field.  The seven terminals here and the honest
  round messages of `CommittedTerminalController` are instances of it.
* **The seven lane terminals.**  `laneTerminalKind` walks the gate list for
  each op-selected operand terminal (gamma-weighted except `mulB`) and the
  root-pin list for `zero`; `read_laneTerminalKind` reads each to
  `(terminalFunctional kind ...).eval (liftWord wv)`, the exact affine
  functional the controller's eta relation names; `laneTerminal7` is the
  receipt's `Fin 7` order.
* **`TerminalOpenings` inhabited** from the opened word
  (`terminalOpeningsOfLanes`); `factoredRounds_terminal_of_openings` (REUSED)
  then closes the factored quadratic chain at the lane expression
  (`factored7_closes`).
* **The realizer.**  `realize7` recommits the word and recomputes the seven;
  `realize7_sound` under the named `BindingCommitment` gives the seven at the
  COMMITTED trace, `terminalOpeningsOfBinding` inhabits the interface there,
  and `factored7_closes_realized` closes the zero-anchored factored chain of
  a satisfying trace at `terminalExpression` of the realized values -- the
  factored analogue of `honestRounds_closes_realized`.

**The statement the unit was handed, corrected before proof.**  "The factored
product equals the single realized terminal" is FALSE off the cube:
`mle A r * mle B r` is not `mle (A * B) r` -- the MLE of a product is not the
product of MLEs, and `GateMleExt6` §3 says exactly this (the two agree at
Boolean corners; authenticating the factorization off the cube is the seam).
On a satisfying trace the single terminal is `0` (`demo_honest_terminal_zero`)
while the factored expression is generically nonzero:
`DemoInstance.factored7_ne_single` decides the refutation on the emitted demo
descriptor.  The TRUE relation is that each protocol closes against its OWN
terminal from the SAME opened word (`factored7_closes_realized` here,
`honestRounds_closes_realized` in the realizer), and that their zero claims
coincide (`CommittedTerminalCompose.sum_gammaResidualTable`).

**ATLAS fields (law 2), decided by the kernel on `demoDescriptor` (23
residuals, `m = 5`) at `idealCommitment`:** `realize7_complete_demo` (the
honest seven, as pinned LITERALS, accepted), `realize7_refuses_forged_value`
(one of the seven off by one), `realize7_refuses_forged_word` (tampered word
under the honest root), `factored7_ne_single` (the refutation above).  Premise
inhabitation: `idealCommitment`, as in the realizer.  Stage 0 (4,148
residuals, `m = 13`) is a compiled `#eval` with throw-teeth.
-/

import Compiler.CommittedTerminalRealizer
import Compiler.GateFactoredExt6
import Compiler.Ext6GateProofController

namespace Minidregg.Compiler.CommittedTerminalFactored7

open scoped BigOperators
open Minidregg.Assurance Minidregg.Selvage Minidregg.Compiler.GateMleExt6
open Minidregg.Compiler.GateFactoredExt6 Minidregg.Compiler.CommittedTerminalRealizer
open Minidregg.Compiler.Ext6GateProofController (terminalExpression)
open Polynomial

set_option autoImplicit false
set_option maxRecDepth 10000

/-! ## §1. The generic lane walker -/

section Walk

variable {α : Type}

/-- Walk a list with a running gamma power `gpow = gamma^k` and a per-position
weight `wt k`, accumulating `Σ_k f a_k gamma^k · wt k`.  Every product is a
materialized `Ext6L` (strict). -/
def walk (gamma : Ext6L) (f : α → Ext6L → Ext6L) (wt : Nat → Ext6L) :
    List α → Nat → Ext6L → Ext6L → Ext6L
  | [], _, _, acc => acc
  | a :: rest, k, gpow, acc =>
      walk gamma f wt rest (k + 1) (ext6MulL gpow gamma)
        (ext6Add acc (ext6MulL (f a gpow) (wt k)))

/-- The walker read into the field: any lane payload `f` with a field
counterpart `F` and any weight `wt` with counterpart `W`. -/
theorem read_walk (gamma : Ext6L) (f : α → Ext6L → Ext6L) (wt : Nat → Ext6L)
    (F : α → Ext6Q → Ext6Q) (hf : ∀ a p, readExt6 (f a p) = F a (readExt6 p))
    (W : Nat → Ext6Q) (hw : ∀ k, readExt6 (wt k) = W k) (dflt : α) (l : List α) :
    ∀ (k : Nat) (gpow acc : Ext6L),
      readExt6 (walk gamma f wt l k gpow acc) =
        readExt6 acc + ∑ j ∈ Finset.range l.length,
          F (l.getD j dflt) (readExt6 gpow * readExt6 gamma ^ j) * W (k + j) := by
  induction l with
  | nil =>
    intro k gpow acc
    simp [walk]
  | cons a rest ih =>
    intro k gpow acc
    rw [walk, ih, List.length_cons, Finset.sum_range_succ']
    simp only [read_add, read_mul, hf, hw, List.getD_cons_zero, List.getD_cons_succ,
      pow_zero, mul_one, Nat.add_zero]
    have hshift : ∀ j ∈ Finset.range rest.length,
        F (rest.getD j dflt) (readExt6 gpow * readExt6 gamma * readExt6 gamma ^ j) *
            W (k + 1 + j) =
          F (rest.getD j dflt) (readExt6 gpow * readExt6 gamma ^ (j + 1)) *
            W (k + (j + 1)) := by
      intro j _
      rw [show k + 1 + j = k + (j + 1) by omega]
      congr 2
      ring
    rw [Finset.sum_congr rfl hshift]
    ring

/-- The walker from a zero accumulator, as a `Fin`-indexed sum over `List.get`. -/
theorem read_walk_fin (gamma : Ext6L) (f : α → Ext6L → Ext6L) (wt : Nat → Ext6L)
    (F : α → Ext6Q → Ext6Q) (hf : ∀ a p, readExt6 (f a p) = F a (readExt6 p))
    (W : Nat → Ext6Q) (hw : ∀ k, readExt6 (wt k) = W k) (dflt : α) (l : List α)
    (k : Nat) (gpow : Ext6L) :
    readExt6 (walk gamma f wt l k gpow ext6Zero) =
      ∑ j : Fin l.length,
        F (l.get j) (readExt6 gpow * readExt6 gamma ^ (j : Nat)) * W (k + j) := by
  rw [read_walk gamma f wt F hf W hw dflt l k gpow ext6Zero, read_zero, zero_add,
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem j.isLt, Option.getD_some,
    List.get_eq_getElem]

end Walk

/-! ## §2. The seven lane terminals -/

section Seven

variable {m : Nat}

/-- Sparse-table MLE evaluation as the sum over the payload list (the
computation inside `mle_operandTable_eq_selectorFunctional_eval`, exposed). -/
theorem mle_operandTable_sparse {t : Nat} (enc : Fin t ↪ (Fin m → Bool))
    (scale : Fin t → Ext6Q) (operand : Fin t → DWire BabyBear) (wv : Nat → BabyBear)
    (r : Fin m → Ext6Q) :
    mle (operandTable enc scale operand wv) r =
      ∑ k, scale k * algebraMap BabyBear Ext6Q ((operand k).read wv) * chiEval (enc k) r := by
  classical
  rw [mle]
  unfold operandTable sparseTable
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Fintype.sum_eq_single (enc k)]
  · simp
  · intro b hb
    simp [Ne.symm hb]

@[simp] theorem gateEncoding_apply (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m → Bool)) (k : Fin d.gates.length) :
    gateEncoding d wv enc k = enc (gatePosition d wv k) := rfl

@[simp] theorem zeroEncoding_apply (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m → Bool)) (j : Fin d.zeros.length) :
    zeroEncoding d wv enc j = enc (zeroPosition d wv j) := rfl

/-- The lane payload of one gate for an op-selected operand terminal:
`gamma^k · read (pick g)` (or `read (pick g)` unweighted) when the op matches,
`0` otherwise -- `gateOpScale` in lanes. -/
def gatePayload (wv : Nat → BabyBear) (wanted : GateOp) (weighted : Bool)
    (pick : DGate BabyBear → DWire BabyBear) (g : DGate BabyBear) (gpow : Ext6L) : Ext6L :=
  if g.op = wanted then
    ext6MulL (if weighted then gpow else ext6One) (ext6OfBase ((pick g).read wv))
  else ext6Zero

/-- Its field counterpart. -/
noncomputable def gatePayloadF (wv : Nat → BabyBear) (wanted : GateOp) (weighted : Bool)
    (pick : DGate BabyBear → DWire BabyBear) (g : DGate BabyBear) (p : Ext6Q) : Ext6Q :=
  if g.op = wanted then
    (if weighted then p else 1) * algebraMap BabyBear Ext6Q ((pick g).read wv)
  else 0

theorem read_gatePayload (wv : Nat → BabyBear) (wanted : GateOp) (weighted : Bool)
    (pick : DGate BabyBear → DWire BabyBear) (g : DGate BabyBear) (gpow : Ext6L) :
    readExt6 (gatePayload wv wanted weighted pick g gpow) =
      gatePayloadF wv wanted weighted pick g (readExt6 gpow) := by
  unfold gatePayload gatePayloadF
  split_ifs <;> simp [read_mul, read_ofBase, read_zero, read_one]

/-- `gamma^k` when weighted, `1` otherwise: the two scale shapes of
`GateFactoredExt6`'s operand tables. -/
noncomputable def scaleOf (weighted : Bool) (gamma : Ext6Q) (k : Nat) : Ext6Q :=
  if weighted then gamma ^ k else 1

/-- One op-selected operand terminal, walked over the gate list from position `0`. -/
def laneGateTerminal (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear) (gamma : Ext6L)
    (r : Fin m → Ext6L) (encNat : Nat → (Fin m → Bool)) (wanted : GateOp) (weighted : Bool)
    (pick : DGate BabyBear → DWire BabyBear) : Ext6L :=
  walk gamma (gatePayload wv wanted weighted pick) (fun k => laneChi (encNat k) r)
    d.gates 0 ext6One ext6Zero

def dummyGate : DGate BabyBear := ⟨.add, .cnst 0, .cnst 0, 0⟩

theorem read_laneGateTerminal (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m → Bool))
    (encNat : Nat → (Fin m → Bool)) (hEnc : ∀ k, enc k = encNat k)
    (gamma : Ext6L) (r : Fin m → Ext6L) (wanted : GateOp) (weighted : Bool)
    (pick : DGate BabyBear → DWire BabyBear) :
    readExt6 (laneGateTerminal d wv gamma r encNat wanted weighted pick) =
      mle (operandTable (gateEncoding d wv enc)
          (gateOpScale d wanted fun k => scaleOf weighted (readExt6 gamma) k.val)
          (fun k => pick (d.gates.get k)) wv)
        (fun i => readExt6 (r i)) := by
  rw [mle_operandTable_sparse, laneGateTerminal,
    read_walk_fin gamma (gatePayload wv wanted weighted pick) (fun k => laneChi (encNat k) r)
      (gatePayloadF wv wanted weighted pick) (read_gatePayload wv wanted weighted pick)
      (fun k => chiEval (encNat k) fun i => readExt6 (r i))
      (fun k => read_laneChi (encNat k) r) dummyGate d.gates 0 ext6One]
  apply Finset.sum_congr rfl
  intro k _
  rw [read_one, one_mul, Nat.zero_add, gateEncoding_apply, hEnc, gatePosition_val]
  unfold gatePayloadF gateOpScale scaleOf
  split_ifs <;> ring

/-- The lane payload of one root pin: `gamma^k · read z`. -/
def zeroPayload (wv : Nat → BabyBear) (z : DWire BabyBear) (gpow : Ext6L) : Ext6L :=
  ext6MulL gpow (ext6OfBase (z.read wv))

noncomputable def zeroPayloadF (wv : Nat → BabyBear) (z : DWire BabyBear) (p : Ext6Q) : Ext6Q :=
  p * algebraMap BabyBear Ext6Q (z.read wv)

theorem read_zeroPayload (wv : Nat → BabyBear) (z : DWire BabyBear) (gpow : Ext6L) :
    readExt6 (zeroPayload wv z gpow) = zeroPayloadF wv z (readExt6 gpow) := by
  simp [zeroPayload, zeroPayloadF, read_mul, read_ofBase]

/-- The root-pin terminal, walked over the zero list from position `|gates|`
with the power `gamma^|gates|`, exactly the exponents `zeroGamma` uses. -/
def laneZeroTerminal (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear) (gamma : Ext6L)
    (r : Fin m → Ext6L) (encNat : Nat → (Fin m → Bool)) : Ext6L :=
  walk gamma (zeroPayload wv) (fun k => laneChi (encNat k) r)
    d.zeros d.gates.length (ext6Pow gamma d.gates.length) ext6Zero

theorem read_laneZeroTerminal (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m → Bool))
    (encNat : Nat → (Fin m → Bool)) (hEnc : ∀ k, enc k = encNat k)
    (gamma : Ext6L) (r : Fin m → Ext6L) :
    readExt6 (laneZeroTerminal d wv gamma r encNat) =
      mle (zeroGamma d wv enc (readExt6 gamma)) (fun i => readExt6 (r i)) := by
  rw [zeroGamma, mle_operandTable_sparse, laneZeroTerminal,
    read_walk_fin gamma (zeroPayload wv) (fun k => laneChi (encNat k) r)
      (zeroPayloadF wv) (read_zeroPayload wv)
      (fun k => chiEval (encNat k) fun i => readExt6 (r i))
      (fun k => read_laneChi (encNat k) r) (DWire.cnst 0) d.zeros d.gates.length
      (ext6Pow gamma d.gates.length)]
  apply Finset.sum_congr rfl
  intro j _
  rw [read_pow, ← pow_add, zeroEncoding_apply, hEnc, zeroPosition_val]
  unfold zeroPayloadF
  ring

/-- **The seven, by kind.** -/
def laneTerminalKind (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear) (gamma : Ext6L)
    (r : Fin m → Ext6L) (encNat : Nat → (Fin m → Bool)) : TerminalKind → Ext6L
  | .mulA => laneGateTerminal d wv gamma r encNat .mul true (·.a)
  | .mulB => laneGateTerminal d wv gamma r encNat .mul false (·.b)
  | .mulC => laneGateTerminal d wv gamma r encNat .mul true (fun g => .wire g.out)
  | .addA => laneGateTerminal d wv gamma r encNat .add true (·.a)
  | .addB => laneGateTerminal d wv gamma r encNat .add true (·.b)
  | .addC => laneGateTerminal d wv gamma r encNat .add true (fun g => .wire g.out)
  | .zero => laneZeroTerminal d wv gamma r encNat

/-- **The seven, in the receipt's `terminalOrder`.** -/
def laneTerminal7 (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear) (gamma : Ext6L)
    (r : Fin m → Ext6L) (encNat : Nat → (Fin m → Bool)) (j : Fin 7) : Ext6L :=
  laneTerminalKind d wv gamma r encNat (terminalOrder j)

/-- The receipt position of each kind: the inverse of `terminalOrder`. -/
def kindIndex : TerminalKind → Fin 7
  | .mulA => 0 | .mulB => 1 | .mulC => 2 | .addA => 3 | .addB => 4 | .addC => 5 | .zero => 6

theorem terminalOrder_kindIndex (kind : TerminalKind) : terminalOrder (kindIndex kind) = kind := by
  cases kind <;> rfl

/-- **The bridge, by kind:** each lane terminal reads to the exact affine
functional of the trace the controller's eta relation names. -/
theorem read_laneTerminalKind (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m → Bool))
    (encNat : Nat → (Fin m → Bool)) (hEnc : ∀ k, enc k = encNat k)
    (gamma : Ext6L) (r : Fin m → Ext6L) (kind : TerminalKind) :
    readExt6 (laneTerminalKind d wv gamma r encNat kind) =
      (terminalFunctional kind d wv enc (readExt6 gamma) (fun i => readExt6 (r i))).eval
        (liftWord (K := Ext6Q) wv) := by
  cases kind <;>
    simp only [laneTerminalKind, terminalFunctional] <;>
    rw [← mle_operandTable_eq_selectorFunctional_eval]
  · rw [read_laneGateTerminal d wv enc encNat hEnc]; simp [scaleOf]
  · rw [read_laneGateTerminal d wv enc encNat hEnc]; simp [scaleOf]
  · rw [read_laneGateTerminal d wv enc encNat hEnc]; simp [scaleOf]
  · rw [read_laneGateTerminal d wv enc encNat hEnc]; simp [scaleOf]
  · rw [read_laneGateTerminal d wv enc encNat hEnc]; simp [scaleOf]
  · rw [read_laneGateTerminal d wv enc encNat hEnc]; simp [scaleOf]
  · exact read_laneZeroTerminal d wv enc encNat hEnc gamma r

theorem read_laneTerminal7 (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m → Bool))
    (encNat : Nat → (Fin m → Bool)) (hEnc : ∀ k, enc k = encNat k)
    (gamma : Ext6L) (r : Fin m → Ext6L) (j : Fin 7) :
    readExt6 (laneTerminal7 d wv gamma r encNat j) =
      (terminalFunctional (terminalOrder j) d wv enc (readExt6 gamma)
        (fun i => readExt6 (r i))).eval (liftWord (K := Ext6Q) wv) :=
  read_laneTerminalKind d wv enc encNat hEnc gamma r (terminalOrder j)

/-- The controller's `terminalExpression`, in lanes. -/
def laneTerminalExpression (v : Fin 7 → Ext6L) : Ext6L :=
  ext6Add (ext6Sub (ext6Add (ext6Add (ext6Sub (ext6MulL (v 0) (v 1)) (v 2)) (v 3)) (v 4))
    (v 5)) (v 6)

theorem read_laneTerminalExpression (v : Fin 7 → Ext6L) :
    readExt6 (laneTerminalExpression v) = terminalExpression (fun j => readExt6 (v j)) := by
  simp [laneTerminalExpression, terminalExpression, read_add, read_sub, read_mul]

/-! ## §3. `TerminalOpenings` inhabited from the opened word; the factored chain closes -/

/-- The commitment layer's interface, inhabited by the lanes: each opening is
the lane value minus the public constant. -/
noncomputable def terminalOpeningsOfLanes (d : ConstraintDescriptor BabyBear)
    (wv : Nat → BabyBear) (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m → Bool))
    (encNat : Nat → (Fin m → Bool)) (hEnc : ∀ k, enc k = encNat k)
    (gamma : Ext6L) (r : Fin m → Ext6L) :
    TerminalOpenings d wv enc (readExt6 gamma) (fun i => readExt6 (r i)) where
  openLinear kind :=
    { value := readExt6 (laneTerminalKind d wv gamma r encNat kind) -
        (terminalFunctional kind d wv enc (readExt6 gamma) (fun i => readExt6 (r i))).constant
      authenticates := by
        rw [read_laneTerminalKind d wv enc encNat hEnc gamma r kind, TraceAffineFunctional.eval]
        ring }

theorem affineValue_ofLanes (d : ConstraintDescriptor BabyBear)
    (wv : Nat → BabyBear) (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m → Bool))
    (encNat : Nat → (Fin m → Bool)) (hEnc : ∀ k, enc k = encNat k)
    (gamma : Ext6L) (r : Fin m → Ext6L) (kind : TerminalKind) :
    (terminalOpeningsOfLanes d wv enc encNat hEnc gamma r).affineValue kind =
      readExt6 (laneTerminalKind d wv gamma r encNat kind) := by
  simp [TerminalOpenings.affineValue, terminalOpeningsOfLanes]

/-- **The factored quadratic chain closes at the seven lane terminals**
(`factoredRounds_terminal_of_openings`, REUSED, at the lane openings). -/
theorem factored7_closes (d : ConstraintDescriptor BabyBear)
    (wv : Nat → BabyBear) (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m → Bool))
    (encNat : Nat → (Fin m → Bool)) (hEnc : ∀ k, enc k = encNat k)
    (gamma : Ext6L) (r : Fin m → Ext6L) :
    scChain (gammaBatchedDescriptorResidual d wv (readExt6 gamma))
        (factoredRounds d wv enc (readExt6 gamma) (chalOf fun i => readExt6 (r i)))
        (chalOf fun i => readExt6 (r i)) m =
      terminalExpression (fun j => readExt6 (laneTerminal7 d wv gamma r encNat j)) := by
  rw [factoredRounds_terminal_of_openings d wv enc _ _
    (terminalOpeningsOfLanes d wv enc encNat hEnc gamma r)]
  simp only [affineValue_ofLanes, terminalExpression]
  rfl

/-! ## §4. The realizer for the seven -/

/-- A full-word opening claiming the seven factored terminals. -/
structure Opening7 (n : Nat) where
  word : Fin n → BabyBear
  values : Fin 7 → Ext6L

/-- **The realizer for the seven**: recommit the word, recompute the seven
from the opened trace, compare with the claims.  Refusals as in `realize`. -/
def realize7 {Root : Type} [DecidableEq Root] {n : Nat}
    (commit : (Fin n → BabyBear) → Root) (d : ConstraintDescriptor BabyBear)
    (encNat : Nat → (Fin m → Bool)) (gamma : Ext6L) (r : Fin m → Ext6L)
    (rt : Root) (op : Opening7 n) : Except Failure (Fin 7 → Ext6L) :=
  if commit op.word ≠ rt then .error .rootMismatch
  else if laneTerminal7 d (traceOf op.word) gamma r encNat ≠ op.values then
    .error .valueMismatch
  else .ok op.values

section Realize7

variable {Root : Type} [DecidableEq Root] {n : Nat}
variable (commit : (Fin n → BabyBear) → Root) (d : ConstraintDescriptor BabyBear)
variable (encNat : Nat → (Fin m → Bool)) (gamma : Ext6L) (r : Fin m → Ext6L)

theorem realize7_ok_iff (rt : Root) (op : Opening7 n) (v : Fin 7 → Ext6L) :
    realize7 commit d encNat gamma r rt op = .ok v ↔
      commit op.word = rt ∧
        laneTerminal7 d (traceOf op.word) gamma r encNat = op.values ∧ v = op.values := by
  unfold realize7
  by_cases hrt : commit op.word = rt
  · by_cases hv : laneTerminal7 d (traceOf op.word) gamma r encNat = op.values
    · simp only [hrt, hv, ne_eq, not_true_eq_false, if_false, Except.ok.injEq, true_and]
      exact eq_comm
    · simp [hrt, hv]
  · simp [hrt]

/-- Completeness in general: the honest seven of any word are accepted. -/
theorem realize7_complete (w : Fin n → BabyBear) :
    realize7 commit d encNat gamma r (commit w)
        ⟨w, laneTerminal7 d (traceOf w) gamma r encNat⟩ =
      .ok (laneTerminal7 d (traceOf w) gamma r encNat) := by
  rw [realize7_ok_iff]
  exact ⟨rfl, rfl, rfl⟩

theorem realize7_wrong_root_refused (rt : Root) (op : Opening7 n)
    (hrt : commit op.word ≠ rt) :
    realize7 commit d encNat gamma r rt op = .error .rootMismatch := by
  unfold realize7
  simp [hrt]

theorem realize7_wrong_value_refused (rt : Root) (op : Opening7 n)
    (hrt : commit op.word = rt)
    (hv : laneTerminal7 d (traceOf op.word) gamma r encNat ≠ op.values) :
    realize7 commit d encNat gamma r rt op = .error .valueMismatch := by
  unfold realize7
  simp [hrt, hv]

end Realize7

section Sound7

variable {Root Op : Type} [DecidableEq Root] {n : Nat}
variable (S : BindingCommitment Root BabyBear (Fin n) Op)
variable (d : ConstraintDescriptor BabyBear)
variable (encNat : Nat → (Fin m → Bool)) (gamma : Ext6L) (r : Fin m → Ext6L)

/-- **Soundness for the seven.**  Against a root committing `w` under the
named `BindingCommitment`, the accepted values ARE the lane terminals of the
COMMITTED trace (a lane-level equality; `commit_injective` is the only
property consumed).  No challenge is drawn; the error is zero, the price is
`[COMMIT-CR]` carried by `S`. -/
theorem realize7_sound (w : Fin n → BabyBear) (op : Opening7 n) (v : Fin 7 → Ext6L)
    (h : realize7 S.commit d encNat gamma r (S.commit w) op = .ok v) :
    v = laneTerminal7 d (traceOf w) gamma r encNat := by
  obtain ⟨hrt, hv, rfl⟩ := (realize7_ok_iff S.commit d encNat gamma r _ op v).mp h
  have hw : op.word = w := S.commit_injective hrt
  rw [← hv, hw]

/-- Read into the field: the accepted seven are the seven affine functionals
of the committed trace, in the receipt's order. -/
theorem realize7_values_eq (w : Fin n → BabyBear) (op : Opening7 n) (v : Fin 7 → Ext6L)
    (h : realize7 S.commit d encNat gamma r (S.commit w) op = .ok v)
    (enc : Fin (descriptorResiduals d (traceOf w)).length ↪ (Fin m → Bool))
    (hEnc : ∀ k, enc k = encNat k) (j : Fin 7) :
    readExt6 (v j) =
      (terminalFunctional (terminalOrder j) d (traceOf w) enc (readExt6 gamma)
        (fun i => readExt6 (r i))).eval (liftWord (K := Ext6Q) (traceOf w)) := by
  rw [realize7_sound S d encNat gamma r w op v h]
  exact read_laneTerminal7 d (traceOf w) enc encNat hEnc gamma r j

/-- **`TerminalOpenings` at the committed trace, from the accepted values**
and the named binding premise: the interface the controller's eta relation
consumes, inhabited by the receipt's own seven values -- no longer on faith. -/
noncomputable def terminalOpeningsOfBinding (w : Fin n → BabyBear) (op : Opening7 n)
    (v : Fin 7 → Ext6L) (h : realize7 S.commit d encNat gamma r (S.commit w) op = .ok v)
    (enc : Fin (descriptorResiduals d (traceOf w)).length ↪ (Fin m → Bool))
    (hEnc : ∀ k, enc k = encNat k) :
    TerminalOpenings d (traceOf w) enc (readExt6 gamma) (fun i => readExt6 (r i)) where
  openLinear kind :=
    { value := readExt6 (v (kindIndex kind)) -
        (terminalFunctional kind d (traceOf w) enc (readExt6 gamma)
          (fun i => readExt6 (r i))).constant
      authenticates := by
        have hv := realize7_values_eq S d encNat gamma r w op v h enc hEnc (kindIndex kind)
        rw [terminalOrder_kindIndex] at hv
        rw [hv, TraceAffineFunctional.eval]
        ring }

theorem affineValue_ofBinding (w : Fin n → BabyBear) (op : Opening7 n)
    (v : Fin 7 → Ext6L) (h : realize7 S.commit d encNat gamma r (S.commit w) op = .ok v)
    (enc : Fin (descriptorResiduals d (traceOf w)).length ↪ (Fin m → Bool))
    (hEnc : ∀ k, enc k = encNat k) (kind : TerminalKind) :
    (terminalOpeningsOfBinding S d encNat gamma r w op v h enc hEnc).affineValue kind =
      readExt6 (v (kindIndex kind)) := by
  simp [TerminalOpenings.affineValue, terminalOpeningsOfBinding]

/-- **The zero-anchored factored chain of a satisfying trace closes at
`terminalExpression` of the realized seven** -- the factored analogue of
`honestRounds_closes_realized`.  This is what replaces the receipt's seven
values taken on faith. -/
theorem factored7_closes_realized (w : Fin n → BabyBear) (op : Opening7 n)
    (v : Fin 7 → Ext6L) (h : realize7 S.commit d encNat gamma r (S.commit w) op = .ok v)
    (enc : Fin (descriptorResiduals d (traceOf w)).length ↪ (Fin m → Bool))
    (hEnc : ∀ k, enc k = encNat k) (hd : descriptorHolds d (traceOf w)) :
    scChain 0 (factoredRounds d (traceOf w) enc (readExt6 gamma) (chalOf fun i => readExt6 (r i)))
        (chalOf fun i => readExt6 (r i)) m =
      terminalExpression (fun j => readExt6 (v j)) := by
  rw [realize7_sound S d encNat gamma r w op v h]
  have hclose := factored7_closes d (traceOf w) enc encNat hEnc gamma r
  rw [gammaBatchedDescriptorResidual_zero_of_holds d (traceOf w) (readExt6 gamma) hd] at hclose
  exact hclose

/-- Refusal through binding: any other word is refused at the root. -/
theorem realize7_other_word_refused (w : Fin n → BabyBear) (op : Opening7 n)
    (hne : op.word ≠ w) :
    realize7 S.commit d encNat gamma r (S.commit w) op = .error .rootMismatch :=
  realize7_wrong_root_refused S.commit d encNat gamma r _ op
    (fun hc => hne (S.commit_injective hc))

end Sound7

end Seven

/-! ## §5. ATLAS fields on the emitted demo descriptor, decided -/

namespace DemoInstance

open CommittedTerminalRealizer.DemoInstance

/-- The honest seven of the demo trace at `gamma = ⟨3,1,4,1,5,9⟩`,
`r i = ⟨i+2,7,1,8,2,8⟩`, as LITERALS (printed once by the compiled lanes, then
pinned; the kernel recomputes them in `realize7_complete_demo`).  The `zero`
terminal is `0`: the demo trace satisfies its root pins. -/
def demoSeven : Fin 7 → Ext6L
  | 0 => ⟨1495293824, 1932395778, 1973594643, 698165895, 745194236, 819932513⟩
  | 1 => ⟨1399047343, 1497969879, 1783299937, 272664844, 1952215852, 481837960⟩
  | 2 => ⟨1641649082, 397369473, 1708446907, 985151120, 986295483, 897852621⟩
  | 3 => ⟨1741396306, 1688691355, 830788138, 98596065, 19106148, 1325682380⟩
  | 4 => ⟨1818845074, 392872317, 476354187, 1542426861, 1020806470, 646195888⟩
  | 5 => ⟨1546975459, 68297751, 1307142325, 1641022926, 1039912618, 1971878268⟩
  | 6 => ⟨0, 0, 0, 0, 0, 0⟩

/-- **Satisfiable, decided:** the honest seven (the pinned literals) are
accepted; the kernel walked the 18 gates six times and the 5 root pins once. -/
theorem realize7_complete_demo :
    realize7 S.commit demoDescriptor (bitCorner 5) gamma r (S.commit demoWord)
        ⟨demoWord, demoSeven⟩ = .ok demoSeven := by
  decide +kernel

/-- **Teeth, decided:** the `mulA` value off by one is refused. -/
theorem realize7_refuses_forged_value :
    realize7 S.commit demoDescriptor (bitCorner 5) gamma r (S.commit demoWord)
        ⟨demoWord, fun j => if j = 0 then ext6Add (demoSeven 0) ext6One else demoSeven j⟩ =
      .error .valueMismatch := by
  decide +kernel

/-- **Teeth, decided:** the tampered word under the honest root is refused at
the root. -/
theorem realize7_refuses_forged_word :
    realize7 S.commit demoDescriptor (bitCorner 5) gamma r (S.commit demoWord)
        ⟨tamperedWord, demoSeven⟩ = .error .rootMismatch := by
  decide +kernel

/-- **The refutation, decided:** on the SAME satisfying trace, at the SAME
`gamma` and `r`, the factored expression of the seven is NONZERO while the
single realized terminal is `0` (`demo_honest_terminal_zero`).  "The factored
product equals the single realized terminal" is false off the cube; the two
protocols have different terminals and each closes against its own. -/
theorem factored7_ne_single : laneTerminalExpression demoSeven ≠ ext6Zero := by
  decide +kernel

end DemoInstance

/-! ## §6. Stage 0: the seven of the 4,131-wire candidate (compiled exhibit) -/

namespace Stage0Exhibit

open CommittedTerminalRealizer.Stage0Exhibit
open Minidregg.Compiler.DescriptorEval Minidregg.Compiler.EvmAddAir

/-- The seven realized on the honest `(1, 2)` candidate (accepted at the ideal
root), the factored expression checked nonzero (so the refutation above is
not a small-instance accident), the forged `Z = 4` word refused at the honest
root and authenticated at its own.  Throws on any deviation. -/
def exhibit : IO Unit := do
  let honest := wordOf (evmAddCandidate 1 2)
  let seven := laneTerminal7 evmAddDescriptor (traceOf honest) gamma r (bitCorner 13)
  match realize7 S.commit evmAddDescriptor (bitCorner 13) gamma r (S.commit honest)
      ⟨honest, seven⟩ with
  | .ok _ => IO.println "stage0 factored7: honest (1, 2) accepted, seven terminals realized"
  | .error e => throw (IO.userError s!"stage0 factored7: honest refused: {repr e}")
  if laneTerminalExpression seven = ext6Zero then
    throw (IO.userError "stage0 factored7: factored expression is 0 on the honest trace")
  IO.println s!"stage0 factored7: factored expression on the honest trace \
    {repr (laneTerminalExpression seven)} (the single terminal is 0)"
  let forged := wordOf (evmAddClaimed 1 2 4)
  match realize7 S.commit evmAddDescriptor (bitCorner 13) gamma r (S.commit honest)
      ⟨forged, seven⟩ with
  | .error .rootMismatch => IO.println "stage0 factored7: forged word refused at the honest root"
  | _ => throw (IO.userError "stage0 factored7: forged word not refused at root")
  let sevenF := laneTerminal7 evmAddDescriptor (traceOf forged) gamma r (bitCorner 13)
  match realize7 S.commit evmAddDescriptor (bitCorner 13) gamma r (S.commit forged)
      ⟨forged, sevenF⟩ with
  | .ok _ => IO.println "stage0 factored7: forged word authenticated at its own root"
  | .error e => throw (IO.userError s!"stage0 factored7: forged self-opening refused: {repr e}")

#eval exhibit

end Stage0Exhibit

#check @read_walk
#check @read_laneTerminalKind
#check @factored7_closes
#check @realize7_sound
#check @factored7_closes_realized

/-- info: 'Minidregg.Compiler.CommittedTerminalFactored7.read_laneTerminalKind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms read_laneTerminalKind
/-- info: 'Minidregg.Compiler.CommittedTerminalFactored7.factored7_closes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms factored7_closes
/-- info: 'Minidregg.Compiler.CommittedTerminalFactored7.realize7_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms realize7_sound
/-- info: 'Minidregg.Compiler.CommittedTerminalFactored7.factored7_closes_realized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms factored7_closes_realized
/-- info: 'Minidregg.Compiler.CommittedTerminalFactored7.DemoInstance.realize7_complete_demo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DemoInstance.realize7_complete_demo
/-- info: 'Minidregg.Compiler.CommittedTerminalFactored7.DemoInstance.realize7_refuses_forged_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DemoInstance.realize7_refuses_forged_value
/-- info: 'Minidregg.Compiler.CommittedTerminalFactored7.DemoInstance.realize7_refuses_forged_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DemoInstance.realize7_refuses_forged_word
/-- info: 'Minidregg.Compiler.CommittedTerminalFactored7.DemoInstance.factored7_ne_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DemoInstance.factored7_ne_single

end Minidregg.Compiler.CommittedTerminalFactored7
