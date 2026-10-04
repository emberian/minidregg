/-
# `StepCases` — the one case split of a demand-machine state

`stepRaw` dispatches on the control, then on the evaluated term's constructor
or on the head frame of the stack.  Every theorem quantified over one raw step
(`typed_stepRaw_preserved`, `graph_stepRaw`, …) needs exactly that split.  It
is written ONCE here: `StepCases P` names one obligation per branch, and
`StepCases.apply` assembles them for every state.

A dispatcher is then a structure instance, one named line per constructor.  A
new `Term` or `Frame` constructor adds one field here and one line to
`StepCases.apply`; every dispatcher then fails with *fields missing:
`evaluate_<new>`*, naming its new obligation, instead of a positional
mismatch inside a nested `cases`.

The module depends only on the machine's types, so a per-constructor case
module may import it without importing any dispatcher (the layout of
PROOF-ENG-DESIGN.md §1(a)).
-/
import Theory.ObjectiveBendDemandMachine
import Theory.AxiomPin

namespace Minidregg.Theory.ObjectiveBendDemandMachine

open ObjectiveBendOpenRecursion

/-- One obligation per branch of `stepRaw`'s dispatch, for a property `P` of
the pre-state. -/
structure StepCases (P : State → Prop) : Prop where
  complete : ∀ s value, s.control = .complete value → P s
  refused : ∀ s reason, s.control = .refused reason → P s
  blackhole : ∀ s address, s.control = .blackhole address → P s
  yielded : ∀ s plan, s.control = .yielded plan → P s
  enter : ∀ s address, s.control = .enter address → P s
  evaluate_bound : ∀ s index env, s.control = .evaluate (.bound index) env → P s
  evaluate_lam : ∀ s body env, s.control = .evaluate (.lam body) env → P s
  evaluate_app : ∀ s function argument env, s.control = .evaluate (.app function argument) env → P s
  evaluate_mix : ∀ s lower upper env, s.control = .evaluate (.mix lower upper) env → P s
  evaluate_fix : ∀ s spec inherited env, s.control = .evaluate (.fix spec inherited) env → P s
  evaluate_specification : ∀ s metadata extension env,
    s.control = .evaluate (.specification metadata extension) env → P s
  evaluate_prototype : ∀ s spec target env, s.control = .evaluate (.prototype spec target) env → P s
  evaluate_reflect : ∀ s target env, s.control = .evaluate (.reflect target) env → P s
  evaluate_metadata : ∀ s target env, s.control = .evaluate (.metadata target) env → P s
  evaluate_project : ∀ s target env, s.control = .evaluate (.project target) env → P s
  evaluate_nat : ∀ s value env, s.control = .evaluate (.nat value) env → P s
  evaluate_boolean : ∀ s value env, s.control = .evaluate (.boolean value) env → P s
  evaluate_label : ∀ s value env, s.control = .evaluate (.label value) env → P s
  evaluate_binary : ∀ s primitive left right env,
    s.control = .evaluate (.binary primitive left right) env → P s
  evaluate_extend : ∀ s target fields env, s.control = .evaluate (.extend target fields) env → P s
  evaluate_record : ∀ s fields env, s.control = .evaluate (.record fields) env → P s
  evaluate_get : ∀ s target name env, s.control = .evaluate (.get target name) env → P s
  evaluate_ifZero : ∀ s value zero successor env,
    s.control = .evaluate (.ifZero value zero successor) env → P s
  evaluate_inject : ∀ s tag payload env, s.control = .evaluate (.inject tag payload) env → P s
  evaluate_case : ∀ s scrutinee arms env, s.control = .evaluate (.case scrutinee arms) env → P s
  evaluate_ifBool : ∀ s condition whenTrue whenFalse env,
    s.control = .evaluate (.ifBool condition whenTrue whenFalse) env → P s
  evaluate_perform : ∀ s plan env, s.control = .evaluate (.perform plan) env → P s
  evaluate_done : ∀ s value env, s.control = .evaluate (.done value) env → P s
  return_nil : ∀ s value, s.control = .returned value → s.stack = [] → P s
  return_argument : ∀ s value argument env rest, s.control = .returned value →
    s.stack = .argument argument env :: rest → P s
  return_update : ∀ s value address rest, s.control = .returned value →
    s.stack = .update address :: rest → P s
  return_field : ∀ s value name rest, s.control = .returned value →
    s.stack = .field name :: rest → P s
  return_reflect : ∀ s value rest, s.control = .returned value → s.stack = .reflect :: rest → P s
  return_metadata : ∀ s value rest, s.control = .returned value → s.stack = .metadata :: rest → P s
  return_project : ∀ s value rest, s.control = .returned value → s.stack = .project :: rest → P s
  return_extend : ∀ s value fields env rest, s.control = .returned value →
    s.stack = .extend fields env :: rest → P s
  return_condition : ∀ s value zero successor env rest, s.control = .returned value →
    s.stack = .condition zero successor env :: rest → P s
  return_binaryLeft : ∀ s value primitive right env rest, s.control = .returned value →
    s.stack = .binaryLeft primitive right env :: rest → P s
  return_binaryRight : ∀ s value primitive left rest, s.control = .returned value →
    s.stack = .binaryRight primitive left :: rest → P s
  return_case : ∀ s value arms env rest, s.control = .returned value →
    s.stack = .case arms env :: rest → P s
  return_ifBool : ∀ s value whenTrue whenFalse env rest, s.control = .returned value →
    s.stack = .ifBool whenTrue whenFalse env :: rest → P s

/-- The only copy of the dispatch tree. -/
theorem StepCases.apply {P : State → Prop} (cases : StepCases P) (s : State) : P s := by
  cases control : s.control with
  | complete value => exact cases.complete s value control
  | refused reason => exact cases.refused s reason control
  | blackhole address => exact cases.blackhole s address control
  | yielded plan => exact cases.yielded s plan control
  | enter address => exact cases.enter s address control
  | evaluate term env =>
      cases term with
      | bound index => exact cases.evaluate_bound s index env control
      | lam body => exact cases.evaluate_lam s body env control
      | app function argument => exact cases.evaluate_app s function argument env control
      | mix lower upper => exact cases.evaluate_mix s lower upper env control
      | fix spec inherited => exact cases.evaluate_fix s spec inherited env control
      | specification metadata extension =>
          exact cases.evaluate_specification s metadata extension env control
      | prototype spec target => exact cases.evaluate_prototype s spec target env control
      | reflect target => exact cases.evaluate_reflect s target env control
      | metadata target => exact cases.evaluate_metadata s target env control
      | project target => exact cases.evaluate_project s target env control
      | nat value => exact cases.evaluate_nat s value env control
      | boolean value => exact cases.evaluate_boolean s value env control
      | label value => exact cases.evaluate_label s value env control
      | binary primitive left right => exact cases.evaluate_binary s primitive left right env control
      | extend target fields => exact cases.evaluate_extend s target fields env control
      | record fields => exact cases.evaluate_record s fields env control
      | get target name => exact cases.evaluate_get s target name env control
      | ifZero value zero successor => exact cases.evaluate_ifZero s value zero successor env control
      | inject tag payload => exact cases.evaluate_inject s tag payload env control
      | case scrutinee arms => exact cases.evaluate_case s scrutinee arms env control
      | ifBool condition whenTrue whenFalse =>
          exact cases.evaluate_ifBool s condition whenTrue whenFalse env control
      | perform plan => exact cases.evaluate_perform s plan env control
      | done value => exact cases.evaluate_done s value env control
  | returned value =>
      cases stack : s.stack with
      | nil => exact cases.return_nil s value control stack
      | cons frame rest =>
          cases frame with
          | argument argument env => exact cases.return_argument s value argument env rest control stack
          | update address => exact cases.return_update s value address rest control stack
          | field name => exact cases.return_field s value name rest control stack
          | reflect => exact cases.return_reflect s value rest control stack
          | metadata => exact cases.return_metadata s value rest control stack
          | project => exact cases.return_project s value rest control stack
          | extend fields env => exact cases.return_extend s value fields env rest control stack
          | condition zero successor env =>
              exact cases.return_condition s value zero successor env rest control stack
          | binaryLeft primitive right env =>
              exact cases.return_binaryLeft s value primitive right env rest control stack
          | binaryRight primitive left => exact cases.return_binaryRight s value primitive left rest control stack
          | case arms env => exact cases.return_case s value arms env rest control stack
          | ifBool whenTrue whenFalse env =>
              exact cases.return_ifBool s value whenTrue whenFalse env rest control stack

#assert_axioms StepCases.apply

end Minidregg.Theory.ObjectiveBendDemandMachine
