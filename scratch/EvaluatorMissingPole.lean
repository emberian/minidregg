/- K-EVAL falsifier (not in any umbrella): Nock with every field but the pole.
   Expected: elaboration error, fields missing: exhausted_says_nothing. -/
import Compiler.Evaluator
open Minidregg.Compiler

def noPole : Evaluator where
  name := "nock-without-pole"
  semantics := Evaluator.nock.semantics
  Term := Evaluator.nock.Term
  Output := Evaluator.nock.Output
  Spec := Evaluator.nock.Spec
  Crash := Evaluator.nock.Crash
  run := Evaluator.nock.run
  steps := Evaluator.nock.steps
  run_sound := Evaluator.nock.run_sound
  run_complete := Evaluator.nock.run_complete
  spec_deterministic := Evaluator.nock.spec_deterministic
  run_crash_iff := Evaluator.nock.run_crash_iff
  crash_not_spec := Evaluator.nock.crash_not_spec
  run_fuel_monotone := Evaluator.nock.run_fuel_monotone
  steps_stable := Evaluator.nock.steps_stable
  Code := Evaluator.nock.Code
  decode := Evaluator.nock.decode
  canonical := Evaluator.nock.canonical
  canonical_unique := Evaluator.nock.canonical_unique
  Input := Evaluator.nock.Input
  encodeInput := Evaluator.nock.encodeInput
  encodeInput_injective := Evaluator.nock.encodeInput_injective
  encodeOutput := Evaluator.nock.encodeOutput
  encodeOutput_injective := Evaluator.nock.encodeOutput_injective
  decodeTerm := Evaluator.nock.decodeTerm
  runBytes := Evaluator.nock.runBytes
  runBytes_sound := Evaluator.nock.runBytes_sound
  runBytes_crash_sound := Evaluator.nock.runBytes_crash_sound
  exportFn := Evaluator.nock.exportFn
  export_is_run := Evaluator.nock.export_is_run
