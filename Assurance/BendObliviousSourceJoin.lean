/- Conditional join of the ACTUAL emitted controller DAG, physical codec,
and source refinement. The required per-block equation is stated explicitly:
no general codec/controller conformance theorem is claimed here. This clear
interpreter is for conformance, not a private protocol or a second evaluator. -/
import Compiler.BendObliviousController
import Compiler.BendObliviousCodec
import Theory.BendClosureSupportedRun

namespace Minidregg.Assurance.BendObliviousSourceJoin
open Minidregg.Theory BendTT BendClosureMachine BendClosureSimulation
open Minidregg.Compiler
set_option autoImplicit false

/-- Every block reads one encoding of the same actual input state. The first
output is a handled bit; unsupported control never becomes successful output. -/
def decodedStep (shape : BendObliviousState.Shape) (library : Library)
    (state : State) : Option State := do
  let network ← BendObliviousController.network shape library
  let input ← BendObliviousCodec.encode shape state
  let output ← network.evaluate input
  if output[0]? == some true then
    BendObliviousCodec.decode shape (output.extract 1 output.size)
  else none

def decodedRun (shape : BendObliviousState.Shape) (library : Library) : Nat → State → Option State
  | 0, state => some state
  | ticks + 1, state => do
      let next ← decodedStep shape library state
      decodedRun shape library ticks next

/-- The conformance premise is a literal equation for the existing DAG and
codec at every actual machine state. Establishing it for arbitrary well-formed
reachable states is an outstanding producer obligation, not this conclusion. -/
theorem decoded_run_exact (shape : BendObliviousState.Shape) (limits : Limits)
    (library : Library) (ticks : Nat) (state : State)
    (conformance : ∀ tick, tick < ticks →
      decodedStep shape library (run limits library tick state) =
        some (step limits library (run limits library tick state))) :
    decodedRun shape library ticks state = some (run limits library ticks state) := by
  induction ticks generalizing state with
  | zero => rfl
  | succ ticks ih =>
    have first : decodedStep shape library state = some (step limits library state) :=
      conformance 0 (Nat.zero_lt_succ _)
    simp only [decodedRun, first, Option.bind_some]
    apply ih
    intro tick less
    simpa only [run] using conformance (tick + 1) (Nat.succ_lt_succ less)

/-- A decoded circuit result preserves the real source prefix when BOTH
explicit obligations hold: graph/codec conformance and source branch coverage.
Neither obligation is silently promoted to universal controller correctness. -/
theorem decoded_source_invariant {book : Book} (shape : BendObliviousState.Shape)
    (limits : Limits) (library : Library) (ticks : Nat) (state result : State)
    (origin : Term) (initialCount : Nat)
    (invariant : SourceInvariant book library.program origin initialCount state)
    (coverage : Covered book limits library ticks state)
    (conformance : ∀ tick, tick < ticks →
      decodedStep shape library (run limits library tick state) =
        some (step limits library (run limits library tick state)))
    (accepted : decodedRun shape library ticks state = some result) :
    SourceInvariant book library.program origin initialCount result := by
  have same := decoded_run_exact shape limits library ticks state conformance
  rw [same] at accepted
  cases Option.some.inj accepted
  exact invariant.run ticks coverage

/-- Physical chaining keeps raw output state bits between blocks. It does not
decode and reencode them on a host between private ticks. -/
def circuitStep (shape : BendObliviousState.Shape) (library : Library)
    (input : Array Bool) : Option (Array Bool) := do
  let network ← BendObliviousController.network shape library
  let output ← network.evaluate input
  if output[0]? == some true then some (output.extract 1 output.size) else none

def circuitRun (shape : BendObliviousState.Shape) (library : Library) :
    Nat → Array Bool → Option (Array Bool)
  | 0, input => some input
  | ticks + 1, input => do
      let next ← circuitStep shape library input
      circuitRun shape library ticks next

/-- Raw padding is deliberately noncanonical: inactive control and popped
stack fields can retain old bits. Conformance therefore relates decode results
on the actual raw reachable prefix, never canonical encode-output equality. -/
theorem circuit_run_decoded (shape : BendObliviousState.Shape) (limits : Limits)
    (library : Library) (ticks : Nat) (state : State) (input : Array Bool)
    (initialDecoded : BendObliviousCodec.decode shape input = some state)
    (conformance : ∀ tick, tick < ticks → ∀ bits,
      circuitRun shape library tick input = some bits →
      BendObliviousCodec.decode shape bits = some (run limits library tick state) →
      ∃ output, circuitStep shape library bits = some output ∧
        BendObliviousCodec.decode shape output =
          some (step limits library (run limits library tick state))) :
    ∃ output, circuitRun shape library ticks input = some output ∧
      BendObliviousCodec.decode shape output = some (run limits library ticks state) := by
  induction ticks generalizing state input with
  | zero => exact ⟨input, rfl, initialDecoded⟩
  | succ ticks ih =>
    obtain ⟨next, nextStep, nextDecoded⟩ :=
      conformance 0 (Nat.zero_lt_succ _) input rfl initialDecoded
    obtain ⟨output, rest, finalDecoded⟩ := ih (step limits library state) next nextDecoded
      (by
        intro tick less bits reached currentDecoded
        have originalReached : circuitRun shape library (tick + 1) input = some bits := by
          simpa only [circuitRun, nextStep, Option.bind_some] using reached
        simpa only [run] using
          conformance (tick + 1) (Nat.succ_lt_succ less) bits originalReached currentDecoded)
    exact ⟨output, by simp only [circuitRun, nextStep, Option.bind_some, rest], finalDecoded⟩

/-- Source receiving for the actual raw physical pipeline. The literal
decode/step equation is restricted to raw states reached by that same pipeline.
Its general producer proof and source coverage remain explicit obligations. -/
theorem circuit_source_invariant {book : Book} (shape : BendObliviousState.Shape)
    (limits : Limits) (library : Library) (ticks : Nat) (state result : State)
    (origin : Term) (initialCount : Nat) (input output : Array Bool)
    (invariant : SourceInvariant book library.program origin initialCount state)
    (coverage : Covered book limits library ticks state)
    (initialDecoded : BendObliviousCodec.decode shape input = some state)
    (conformance : ∀ tick, tick < ticks → ∀ bits,
      circuitRun shape library tick input = some bits →
      BendObliviousCodec.decode shape bits = some (run limits library tick state) →
      ∃ next, circuitStep shape library bits = some next ∧
        BendObliviousCodec.decode shape next =
          some (step limits library (run limits library tick state)))
    (accepted : circuitRun shape library ticks input = some output)
    (decoded : BendObliviousCodec.decode shape output = some result) :
    SourceInvariant book library.program origin initialCount result := by
  obtain ⟨actualOutput, executed, finalDecoded⟩ :=
    circuit_run_decoded shape limits library ticks state input initialDecoded conformance
  rw [accepted] at executed
  cases Option.some.inj executed
  rw [decoded] at finalDecoded
  cases Option.some.inj finalDecoded
  exact invariant.run ticks coverage

#assert_axioms circuit_run_decoded
#assert_axioms circuit_source_invariant
#assert_axioms decoded_run_exact
#assert_axioms decoded_source_invariant
end Minidregg.Assurance.BendObliviousSourceJoin
