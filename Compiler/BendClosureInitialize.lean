/- Clear, checked source-input initialization for the current BendTT machine.
The actual loader and Machine.bind allocate the rows. Semantic reification of
those actual rows validates the source basis; no caller supplies the environment
meaning. This is an embedded-profile reference/admission producer, not a private
input protocol or a theorem about the future Objective language. -/
import Compiler.BendClosureInput
import Theory.BendClosureControlSteps

namespace Minidregg.Compiler.BendClosureInitialize
open Minidregg.Theory BendTT BendClosureArena BendClosureMachine
open BendClosureSimulation BendClosureInput
set_option autoImplicit false

structure Initialized (limits : Limits) (library : Library) (entry : Nat)
    (template : Term) (tree : DataTree) where
  loaded : LoadedState library.program tree
  bound : State
  environment : Nat
  emptyPreserved : loaded.state.heap.get? 0 = some .nil
  bindExact : (BendClosureMachine.bind limits library .Q2 loaded.pointer 0).run loaded.state =
    .ok (environment, bound)
  codeExact : CodeDenotes library.program entry template
  inputExact : Denotes library.program bound.heap loaded.pointer tree.source
  environmentExact : EnvironmentDenotes library.program bound.heap environment [tree.source]
  stackEmpty : bound.stack = []
  countZero : bound.sourceSteps = 0

def Initialized.state {limits : Limits} {library : Library} {entry : Nat}
    {template : Term} {tree : DataTree} (result : Initialized limits library entry template tree) : State :=
  {result.bound with control := .evaluate entry result.environment}

theorem Initialized.denotes {limits : Limits} {library : Library} {entry : Nat}
    {template : Term} {tree : DataTree} {book : Book}
    (result : Initialized limits library entry template tree) :
    StateDenotes book library.program result.state
      (Term.sub (Env.sub [tree.source]) template) := by
  have stack : StackDenotes book library.program result.state.heap result.state.stack [] := by
    simpa [Initialized.state, result.stackEmpty] using
      (show StackDenotes book library.program result.bound.heap [] [] from .nil)
  simpa [plug] using (evaluate_state (state := result.state) (book := book)
    (contexts := []) rfl (.exact result.codeExact result.environmentExact) stack)

theorem Initialized.source_count {limits : Limits} {library : Library} {entry : Nat}
    {template : Term} {tree : DataTree} (result : Initialized limits library entry template tree) :
    result.state.sourceSteps = 0 := result.countZero

/-- Failures include missing admitted literals, real capacity/cache refusal and
any source mismatch during row reification. Successful output retains the exact
Machine.bind equation, not an alternative manually constructed environment. -/
def initializeLoaded (limits : Limits) (library : Library) (entry : Nat)
    (template : Term) (tree : DataTree) : Except BendClosureInput.Failure (Initialized limits library entry template tree) := do
  let some code := decodeCode library.program (library.program.code.size + 1) entry
    | throw .validation
  if codeSame : code.term = template then
    let state ← (BendClosureMachine.start limits library entry).mapError BendClosureInput.Failure.machine
    let loaded ← loadState limits library state 0 tree
    if empty : loaded.state.heap.get? 0 = some .nil then
      match binding : (BendClosureMachine.bind limits library .Q2 loaded.pointer 0).run loaded.state with
      | .error reason => throw (.machine reason)
      | .ok (environment, bound) =>
        if stack : bound.stack = [] then
          if steps : bound.sourceSteps = 0 then
            let fuel := bound.heap.used + library.program.code.size + 1
            let some captured := decodeEnvironment library.program bound.heap fuel environment
              | throw .validation
            if envSame : captured.values = [tree.source] then
              let some input := decode library.program bound.heap fuel loaded.pointer
                | throw .validation
              if inputSame : input.term = tree.source then
                pure ⟨loaded, bound, environment, empty, binding, codeSame ▸ code.exact, inputSame ▸ input.exact, envSame ▸ captured.exact, stack, steps⟩
              else throw .validation
            else throw .validation
          else throw .validation
        else throw .validation
    else throw .missingEmptyEnvironment
  else throw .validation

#assert_axioms Initialized.denotes
#assert_axioms Initialized.source_count
end Minidregg.Compiler.BendClosureInitialize
