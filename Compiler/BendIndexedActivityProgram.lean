/- Explicit optimized publication profile for persistent activities.
The signed source record chooses a compiler edition; old Source/prepare remain
available. This producer does not register a native action/evaluator or bypass
source publication, current permission, funding or custody admission.
-/
import Compiler.BendActivityProgram
import Compiler.BendIndexedExecutionContext

namespace Minidregg.Compiler.BendIndexedActivityProgram
open Minidregg.Theory
open BendTT BendClosureArena BendClosureMachine
open Minidregg.Compiler.Tower256ConcreteBackend
open BendClosureContinuationCodec
set_option autoImplicit false

structure Source where
  program : BendActivityProgram.Source
  compilerEdition : String

/-- Edition selection is encoded with the full immutable public source record,
so a signed source/action binding cannot omit or silently reinterpret it. -/
def sourceStream : StreamCodec Source :=
  StreamCodec.xmap (StreamCodec.product BendActivityProgram.sourceStream stringStream)
    (fun s => (s.program, s.compilerEdition)) (fun s => ⟨s.1,s.2⟩)
    (by intro s; cases s; rfl)

def binding (source : Source) : List UInt8 :=
  "DREGG.BEND.ACTIVITY.PUBLIC-SOURCE/INDEXED-v1".toUTF8.toList ++ sourceStream.encode source

/-- A signed canonical binding identifies the whole source AND compiler
selection exactly. Digest collision assumptions are not used in this law. -/
theorem binding_injective {left right : Source} (same : binding left = binding right) :
    left = right := by
  unfold binding at same
  have encoded := List.append_cancel_left same
  have decoded := congrArg (fun bytes => sourceStream.decodePrefix (bytes ++ [])) encoded
  change sourceStream.decodePrefix (sourceStream.encode left ++ []) =
    sourceStream.decodePrefix (sourceStream.encode right ++ []) at decoded
  rw [sourceStream.decodePrefix_encode, sourceStream.decodePrefix_encode] at decoded
  exact congrArg Prod.fst (Option.some.inj decoded)

structure Prepared (source : Source) where
  actual : BendActivityProgram.Prepared source.program
  selected : source.compilerEdition = BendClosureCompileIndexed.edition

/-- Exactly the original public admission caps and source witnesses. Only the
publication representation changes; its checker theorem is reused explicitly.
There is no fallback to another compiler/profile if an indexed check refuses. -/
def prepare (source : Source) : Option (Prepared source) := do
  if selected : source.compilerEdition = BendClosureCompileIndexed.edition then
    let program := source.program
    if program.coreBytes.length > 1048576 || program.slots > 65536 || program.wordBits > 64 ||
        program.frames > 65536 || program.arguments > 65536 || program.checkerTicks > 100000 then none else do
      let .ok core := BendCoreAdmission.admit program.coreBytes | none
      if sourceBytes : core.bytes = program.coreBytes then
        let .ok entry := BendCoreAdmission.entry core program.entry | none
        if entryName : entry.name = program.entry then
          let compiled ← BendClosureCompileIndexed.compileChecked core.book (.Ref program.entry) core.checked
          let admitted ← BendInvocationAdmission.admit core.book program.checkerTicks
            (.Ref program.entry) entry.definition.T
          if fits : program.slots ≤ 2 ^ program.wordBits then
            some ⟨⟨core,sourceBytes,entry,entryName,compiled,admitted,
              ⟨⟨program.slots,program.wordBits,fits⟩,program.frames,program.arguments⟩,
              rfl,rfl,rfl,rfl⟩,selected⟩
          else none
        else none
      else none
  else none

/-- Receivers supply this expected context after CURRENT signed admission of
binding(source), not after accepting a checkpoint's self-declared compiler. -/
def contextBytes {source : Source} (prepared : Prepared source) : List UInt8 :=
  BendIndexedExecutionContext.bytes (binding source) prepared.actual.limits prepared.actual.compiled.library

theorem prepared_entry_exact {source : Source} (prepared : Prepared source) :
    CodeDenotes prepared.actual.compiled.library.program prepared.actual.compiled.entry
      (.Ref source.program.entry) := prepared.actual.compiled.exactEntry

theorem prepared_invocation_typed {source : Source} (prepared : Prepared source) :
    Typed prepared.actual.core.book [] (.Ref source.program.entry) prepared.actual.entry.definition.T :=
  prepared.actual.admitted.typed

theorem compiler_selected {source : Source} (prepared : Prepared source) :
    source.compilerEdition = BendClosureCompileIndexed.edition := prepared.selected

theorem unsupported_edition_refused (source : Source)
    (different : source.compilerEdition ≠ BendClosureCompileIndexed.edition) : prepare source = none := by
  simp [prepare, different]

#assert_axioms binding_injective
#assert_axioms prepare
#assert_axioms prepared_entry_exact
#assert_axioms prepared_invocation_typed
#assert_axioms compiler_selected
#assert_axioms unsupported_edition_refused
end Minidregg.Compiler.BendIndexedActivityProgram
