/- General laws for the executable continuation machine. This is an initial
refinement tranche, not the still-required all-opcode forward/backward source
simulation. No theorem below assumes a private oracle or invents admission. -/
import Compiler.BoundedNockNetwork

namespace Minidregg.Assurance.BoundedNockRefinement
open Minidregg.Theory
open BoundedNockMachine
set_option autoImplicit false

theorem runTicks_add (first second : Nat) (state : State) :
    runTicks (first + second) state = runTicks second (runTicks first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, runTicks]
  | succ first ih => simpa only [Nat.succ_add, runTicks] using ih (step state)

/-- Once stopped, padding leaks no later distinction through the result or
native charge. Physical gate scheduling still requires the controller circuit. -/
theorem halt_padding (ticks padding : Nat) (state stopped : State)
    (outcome : Halt) (ran : runTicks ticks state = stopped)
    (halted : stopped.mode = .halted outcome) :
    runTicks (ticks + padding) state = stopped := by
  rw [runTicks_add, ran]
  have eq : stopped = { stopped with mode := .halted outcome } := by
    cases stopped
    simp_all
  conv_rhs => rw [eq]
  conv_lhs => rw [eq]
  exact runTicks_halted padding stopped outcome

/-- Successful parsing of quote charges exactly one native rule and returns the
existing noun pointer without allocation. This holds for every heap/state. -/
theorem quote_microstep (state : State) (subject formula value : Nat)
    (mode : state.mode = .eval subject formula) (fuel : state.remaining ≠ 0)
    (parsed : parse { state with
        remaining := state.remaining - 1
        used := state.used + 1 } formula = some (.quote value)) :
    step state = { state with
      remaining := state.remaining - 1
      used := state.used + 1
      mode := .ret value } := by
  simp only [mode] at parsed
  simp only [step, mode, fuel, ↓reduceIte, parsed, enter]

/-- Native quote source rule. The pointer-to-noun decode/simulation relation
must join this rule to quote_microstep and all other instruction cases. -/
theorem source_quote (subject value : Noun) :
    Nock.Step subject (Noun.cell (Noun.atom 1) value) value := .quote

/-- Native fuel zero is semantic exhaustion without charging another rule. -/
theorem empty_fuel (state : State) (subject formula : Nat)
    (mode : state.mode = .eval subject formula) (fuel : state.remaining = 0) :
    step state = { state with mode := .halted .exhausted } := by
  simp only [step, mode, fuel, ↓reduceIte, stop]

#assert_axioms runTicks_add
#assert_axioms halt_padding
#assert_axioms quote_microstep
#assert_axioms source_quote
#assert_axioms empty_fuel

end Minidregg.Assurance.BoundedNockRefinement
