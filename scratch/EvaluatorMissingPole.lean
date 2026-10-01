/- K-EVAL falsifier (not in any umbrella): Nock with every field but the pole.
   Expected: elaboration error, fields missing: exhausted_says_nothing. -/
import Compiler.Evaluator
open Minidregg.Compiler

def noPole : Evaluator where
  toMachine := { Machine.nock with name := "nock-without-pole" }
  Spec := Evaluator.nock.Spec
  Crash := Evaluator.nock.Crash
  run_sound := Evaluator.nock.run_sound
  run_complete := Evaluator.nock.run_complete
  spec_deterministic := Evaluator.nock.spec_deterministic
  run_crash_iff := Evaluator.nock.run_crash_iff
  crash_not_spec := Evaluator.nock.crash_not_spec
  run_fuel_monotone := Evaluator.nock.run_fuel_monotone
  steps_stable := Evaluator.nock.steps_stable
  canonical_unique := Evaluator.nock.canonical_unique
  encodeInput_injective := Evaluator.nock.encodeInput_injective
  encodeOutput_injective := Evaluator.nock.encodeOutput_injective
  runBytes_sound := Evaluator.nock.runBytes_sound
  runBytes_crash_sound := Evaluator.nock.runBytes_crash_sound
  export_is_run := Evaluator.nock.export_is_run
  decodeTerm_encodeTerm := Evaluator.nock.decodeTerm_encodeTerm
  oracle_ok := Evaluator.nock.oracle_ok
  oracle_crash := Evaluator.nock.oracle_crash
  oracle_exhausted := Evaluator.nock.oracle_exhausted
  oracle_is_export := Evaluator.nock.oracle_is_export
  sampleOf_overMax := Evaluator.nock.sampleOf_overMax
  overMax_congr := Evaluator.nock.overMax_congr
  sampleOf_pinned_of_fields := Evaluator.nock.sampleOf_pinned_of_fields
  staleField_names := Evaluator.nock.staleField_names
