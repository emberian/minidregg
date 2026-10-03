/- The named-call lambda/projection walk preserves transitive capture and
argument readiness. Its source origin stays fixed until the actual leaf commit. -/
import Theory.BendClosureWalkCodeCases

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem ReadyState.walk_lambda {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment original argument body nextEnvironment : Nat) (args : List (Quan × Nat))
    (binder quantity : Quan) (heap : Heap)
    (ready : ReadyState book library.program state source)
    (control : state.control = .walk pc environment original ((quantity,argument) :: args))
    (found : library.program.code[pc]? = some (.lam binder body))
    (compatible : binder.live = quantity.live)
    (copied : binder = .Q2 → state.data[argument]?.getD false = true)
    (room : ((quantity,argument) :: args).length ≤ limits.arguments)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.environment argument environment) = .ok (nextEnvironment,heap)) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic impossible => cases impossible
    | walk code captured originalReady arguments walkPrefix =>
      obtain ⟨f,same,bodyCode⟩ := code.lambda_fields binder body found
      cases same
      cases arguments with
      | cons head tail =>
        have extension := allocate_extends allocated
        have newCaptured := allocate_environment_ready head.2 captured allocated
        have data := fun q2 => cache.sound (cache_bit_of_getD (copied q2)) head.2.denotes
        have certified := cache.allocate false allocated (by intro impossible; cases impossible)
        rw [step_walk_lambda limits library state pc environment original argument body nextEnvironment args
          binder quantity heap control found compatible copied room allocated]
        exact ReadyState.exact (.walk bodyCode newCaptured (originalReady.extends extension)
          (RetainedArguments.extends extension tail) (walkPrefix.lam (by simpa only [← head.1] using compatible) data))
          (stack.extends extension) certified (extension 0 .nil empty)
          (by intro result impossible; cases impossible)

theorem ReadyState.walk_projection {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment original argument handler first second : Nat) (args : List (Quan × Nat))
    (quantity firstQ : Quan)
    (ready : ReadyState book library.program state source)
    (control : state.control = .walk pc environment original ((quantity,argument) :: args))
    (found : library.program.code[pc]? = some (.prj handler))
    (live : quantity.live = true)
    (rowFound : state.heap.get? argument = some (.pair firstQ first second))
    (room : ((quantity,argument) :: args).length ≤ limits.arguments)
    (expandedRoom : ((Quan.fld firstQ quantity,first) :: (quantity,second) :: args).length ≤ limits.arguments) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic impossible => cases impossible
    | walk code captured originalReady arguments walkPrefix =>
      obtain ⟨f,same,handlerCode⟩ := code.projection_fields handler found
      cases same
      cases arguments with
      | cons head tail =>
        rename_i sourceArgument remainingArguments
        rcases sourceArgument with ⟨sourceQ,sourceTerm⟩
        have sameQ : quantity = sourceQ := head.1
        cases sameQ
        obtain ⟨a,b,sourceSame,firstReady,secondReady,pairValue⟩ := RetainedReady.pair_fields head.2 rowFound
        cases sourceSame
        have nextPrefix := walkPrefix.prj live
        rw [step_walk_projection limits library state pc environment original argument handler first second args
          quantity firstQ control found live rowFound room expandedRoom]
        exact ReadyState.exact (.walk handlerCode captured originalReady
          (.cons ⟨rfl,firstReady⟩ (.cons ⟨rfl,secondReady⟩ tail)) nextPrefix)
          stack cache empty (by intro result impossible; cases impossible)

#assert_axioms ReadyState.walk_lambda
#assert_axioms ReadyState.walk_projection
end Minidregg.Theory.BendClosureSimulation
