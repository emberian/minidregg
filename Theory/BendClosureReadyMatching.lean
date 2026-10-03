/- Exact string-labelled matching preserves reachable-state readiness both
inside a named case tree and in ordinary application. -/
import Theory.BendClosureReadyNamedCall
import Theory.BendClosureWalkMatching

namespace Minidregg.Theory.BendClosureArena
open BendTT
set_option autoImplicit false

theorem CodeDenotes.matching_fields {program : Program} {pointer : Nat} {source : Term}
    (label yes no : Nat) (name : String) (exact : CodeDenotes program pointer source)
    (found : program.code[pointer]? = some (.mat label yes no))
    (named : program.names[label]? = some name) :
    ∃ h m, source = .Mat name h m ∧ CodeDenotes program yes h ∧ CodeDenotes program no m := by
  cases exact <;> simp_all
  exact ⟨_,_,⟨Eq.refl _,Eq.refl _⟩,by assumption,by assumption⟩

#assert_axioms CodeDenotes.matching_fields
end Minidregg.Theory.BendClosureArena

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem Denotes.label_name {program : Program} {heap : Heap}
    {pointer pc environment index : Nat} {source : Term} {name : String}
    (meaning : Denotes program heap pointer source)
    (row : heap.get? pointer = some (.closure pc environment))
    (instruction : program.code[pc]? = some (.lab index))
    (named : program.names[index]? = some name) : source = .Lab name := by
  cases meaning with
  | pair other first second => rw [row] at other; cases other
  | application other function argument => rw [row] at other; cases other
  | closure other code captured =>
    rw [row] at other
    cases other
    have same := CodeDenotes.functional code (.lab instruction named)
    cases same
    rfl

theorem ReadyState.walk_matching {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment original argument label yes no argumentPC argumentEnvironment actualLabel : Nat)
    (q : Quan) (args : List (Quan × Nat)) (wantedName actualName : String)
    (ready : ReadyState book library.program state source)
    (control : state.control = .walk pc environment original ((q,argument) :: args))
    (instruction : library.program.code[pc]? = some (.mat label yes no))
    (argumentRow : state.heap.get? argument = some (.closure argumentPC argumentEnvironment))
    (argumentCode : library.program.code[argumentPC]? = some (.lab actualLabel))
    (wanted : library.program.names[label]? = some wantedName)
    (actual : library.program.names[actualLabel]? = some actualName)
    (live : q.live = true) (room : ((q,argument) :: args).length ≤ limits.arguments) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic impossible => cases impossible
    | walk code captured originalReady arguments walkPrefix =>
      obtain ⟨h,m,same,yesCode,noCode⟩ := code.matching_fields label yes no wantedName instruction wanted
      cases same
      cases arguments with
      | cons head tail =>
        rename_i sourceArgument remainingArguments
        rcases sourceArgument with ⟨sourceQ,sourceTerm⟩
        have sameQ : q = sourceQ := head.1
        cases sameQ
        have sameTerm := Denotes.label_name head.2.denotes argumentRow argumentCode actual
        cases sameTerm
        rw [step_walk_matching limits library state pc environment original argument label yes no argumentPC
          argumentEnvironment actualLabel q args wantedName actualName control instruction argumentRow argumentCode wanted actual live room]
        by_cases sameName : actualName = wantedName
        · rw [if_pos sameName]
          cases sameName
          exact ReadyState.exact (.walk yesCode captured originalReady tail (walkPrefix.hit live)) stack cache empty
            (by intro result impossible; cases impossible)
        · rw [if_neg sameName]
          exact ReadyState.exact (.walk noCode captured originalReady (.cons head tail) (walkPrefix.miss live sameName))
            stack cache empty (by intro result impossible; cases impossible)

theorem ReadyState.matching {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (function argument pc environment label yes no argumentPC argumentEnvironment actualLabel : Nat)
    (q : Quan) (wantedName actualName : String)
    (ready : ReadyState book library.program state source)
    (control : state.control = .apply q function argument)
    (functionRow : state.heap.get? function = some (.closure pc environment))
    (instruction : library.program.code[pc]? = some (.mat label yes no))
    (argumentRow : state.heap.get? argument = some (.closure argumentPC argumentEnvironment))
    (argumentCode : library.program.code[argumentPC]? = some (.lab actualLabel))
    (wanted : library.program.names[label]? = some wantedName)
    (actual : library.program.names[actualLabel]? = some actualName)
    (live : q.live = true) (room : actualName ≠ wantedName → state.stack.length < limits.frames) :
    ∃ nextSource, ReadyState book library.program (step limits library state) nextSource ∧ Eval book source nextSource := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic focus =>
      cases focus with
      | apply functionReady argumentReady functionValue argumentValue =>
        cases functionReady with
        | pair other first second value => rw [functionRow] at other; cases other
        | application other left right value => rw [functionRow] at other; cases other
        | closure other code captured =>
          rw [functionRow] at other
          cases other
          obtain ⟨h,m,same,yesCode,noCode⟩ := code.matching_fields label yes no wantedName instruction wanted
          cases same
          have sameArgument := Denotes.label_name argumentReady.denotes argumentRow argumentCode actual
          cases sameArgument
          by_cases sameName : actualName = wantedName
          · cases sameName
            have sourceStep := (match_hit_source limits library state function argument pc environment label yes no argumentPC
              argumentEnvironment actualLabel q wantedName _ _ _ _ control functionRow instruction argumentRow argumentCode
              wanted actual yesCode noCode captured.denotes argumentReady.denotes stack.denotes live).2.2.1
            refine ⟨_,?_,sourceStep⟩
            rw [step_match_hit limits library state function argument pc environment label yes no argumentPC argumentEnvironment
              actualLabel q wantedName control functionRow instruction argumentRow argumentCode wanted actual live]
            exact ReadyState.exact (.basic (.evaluate yesCode captured)) stack cache empty
              (by intro result impossible; cases impossible)
          · have sourceStep := (match_miss_source limits library state function argument pc environment label yes no argumentPC
              argumentEnvironment actualLabel q wantedName actualName _ _ _ _ control functionRow instruction argumentRow argumentCode
              wanted actual sameName yesCode noCode captured.denotes argumentReady.denotes stack.denotes live (room sameName)).2.2.1
            refine ⟨_,?_,sourceStep⟩
            rw [step_match_miss limits library state function argument pc environment label yes no argumentPC argumentEnvironment
              actualLabel q wantedName actualName control functionRow instruction argumentRow argumentCode wanted actual sameName live (room sameName)]
            exact ReadyState.exact (contexts := .function q (.Lab actualName) :: _)
              (.basic (.evaluate noCode captured)) (.cons (.knownArgument argumentReady) stack) cache empty
              (by intro result impossible; cases impossible)

#assert_axioms Denotes.label_name
#assert_axioms ReadyState.walk_matching
#assert_axioms ReadyState.matching
end Minidregg.Theory.BendClosureSimulation
