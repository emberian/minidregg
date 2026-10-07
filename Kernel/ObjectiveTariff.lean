/- The ONE public tariff of Objective execution: the price of a DECLARED
envelope (`ObjectiveInvocationClaim.Capacity`). Native Objective admission and
the kernel activity (`Kernel.ObjectiveActivity`) both price with it, so there is
one shape for "what a declared envelope costs" (it moved here from
`Kernel.ObjectiveBendNativeAdmission`, unchanged).

Also here: the zero envelope and the field-wise sum of two envelopes (an
activity's resume runs under its escrowed envelope plus what the submitter adds). -/
import Compiler.ObjectiveInvocationClaim
import Theory.AssertAxioms

namespace Minidregg.Kernel.ObjectiveTariff
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
set_option autoImplicit false

/-- The public, versioned price of a DECLARED execution envelope (the charge
law of 2026-10-04): the caller declares its envelope in the signed claim, the
claim's `proofWork` must equal this price of it, execution beyond the envelope
refuses, and nothing is refunded when a run uses less. The price is a function
of the signed public envelope only, never of measured ticks, so a private
branch cannot leak through the charge. `base ≥ 1` (`Tariff.valid`) makes every
admitted invocation cost work: a caller cannot choose zero. -/
structure Tariff where
  version : Nat
  base : Nat
  typeFuel : Nat
  sourceTicks : Nat
  heap : Nat
  stack : Nat
  outputNodes : Nat
  outputBytes : Nat
  /-- The rate per declared extraction tick (`Capacity.extractTicks`). -/
  extractTicks : Nat
  inputBytes : Nat
  deriving DecidableEq, Repr

def tariffStream : StreamCodec Tariff := StreamCodec.xmap
  (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))))))
  (fun t => (t.version,t.base,t.typeFuel,t.sourceTicks,t.heap,t.stack,t.outputNodes,t.outputBytes,t.extractTicks,
    t.inputBytes))
  (fun t => ⟨t.1,t.2.1,t.2.2.1,t.2.2.2.1,t.2.2.2.2.1,t.2.2.2.2.2.1,t.2.2.2.2.2.2.1,t.2.2.2.2.2.2.2.1,
    t.2.2.2.2.2.2.2.2.1,t.2.2.2.2.2.2.2.2.2⟩) (by intro t; cases t; rfl)

/-- The tariff edition this receiver prices with. Edition 2 prices extraction ticks; an
edition-1 tariff (no extraction rate) is refused (`Tariff.valid`). -/
def tariffVersion : Nat := 2

/-- The work units a declared envelope costs. -/
def Tariff.workOf (t : Tariff) (c : ObjectiveInvocationClaim.Capacity) : Nat :=
  t.base + t.typeFuel * c.typeFuel + t.sourceTicks * c.sourceTicks + t.heap * c.heap +
    t.stack * c.stack + t.outputNodes * c.outputNodes + t.outputBytes * c.outputBytes +
    t.extractTicks * c.extractTicks + t.inputBytes * c.inputBytes

def Tariff.valid (t : Tariff) : Bool := t.version == tariffVersion && decide (0 < t.base)

/-- A valid tariff prices every envelope, the empty one included, above zero. -/
theorem Tariff.workOf_pos {t : Tariff} (valid : t.valid = true) (c : ObjectiveInvocationClaim.Capacity) :
    0 < t.workOf c := by
  simp only [Tariff.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
  unfold Tariff.workOf
  omega

/-- Monotone in the envelope: declaring more never costs less. -/
theorem Tariff.workOf_mono (t : Tariff) {a b : ObjectiveInvocationClaim.Capacity}
    (typeFuel : a.typeFuel ≤ b.typeFuel) (sourceTicks : a.sourceTicks ≤ b.sourceTicks)
    (heap : a.heap ≤ b.heap) (stack : a.stack ≤ b.stack) (outputNodes : a.outputNodes ≤ b.outputNodes)
    (outputBytes : a.outputBytes ≤ b.outputBytes) (extractTicks : a.extractTicks ≤ b.extractTicks)
    (inputBytes : a.inputBytes ≤ b.inputBytes) :
    t.workOf a ≤ t.workOf b := by
  unfold Tariff.workOf
  have := Nat.mul_le_mul_left t.typeFuel typeFuel
  have := Nat.mul_le_mul_left t.sourceTicks sourceTicks
  have := Nat.mul_le_mul_left t.heap heap
  have := Nat.mul_le_mul_left t.stack stack
  have := Nat.mul_le_mul_left t.outputNodes outputNodes
  have := Nat.mul_le_mul_left t.outputBytes outputBytes
  have := Nat.mul_le_mul_left t.extractTicks extractTicks
  have := Nat.mul_le_mul_left t.inputBytes inputBytes
  omega

/-- An inhabitant of `Tariff.valid`: one work unit per call and per declared
source tick (the premise of `workOf_pos` is satisfiable). -/
def Tariff.unit : Tariff := ⟨tariffVersion,1,0,1,0,0,0,0,0,0⟩
theorem Tariff.unit_valid : Tariff.unit.valid = true := by decide

open Minidregg.Compiler.ObjectiveInvocationClaim (Capacity) in
/-- The empty envelope. -/
def zeroCapacity : Capacity := ⟨0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0⟩

open Minidregg.Compiler.ObjectiveInvocationClaim (Capacity) in
/-- Two envelopes, field by field. -/
def addCapacity (a b : Capacity) : Capacity :=
  ⟨a.typeFuel + b.typeFuel, a.sourceTicks + b.sourceTicks, a.heap + b.heap, a.stack + b.stack,
    a.outputNodes + b.outputNodes, a.outputBytes + b.outputBytes, a.extractTicks + b.extractTicks,
    a.inputBytes + b.inputBytes,
    a.scalarBits + b.scalarBits, a.memoryTouches + b.memoryTouches, a.proofWork + b.proofWork,
    a.feeDebit + b.feeDebit, a.turnBytes + b.turnBytes, a.witnessBytes + b.witnessBytes,
    a.storageBytes + b.storageBytes, a.sideEffectCount + b.sideEffectCount, a.networkBytes + b.networkBytes,
    a.leaseByteBlocks + b.leaseByteBlocks, a.incidences + b.incidences⟩

#assert_axioms Tariff.workOf_pos
#assert_axioms Tariff.workOf_mono
#assert_axioms Tariff.unit_valid
end Minidregg.Kernel.ObjectiveTariff
