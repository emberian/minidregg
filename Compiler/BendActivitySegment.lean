/- Exact source origins for persistent pure computation segments. A response
starts App Q1 capturedContinuation response, not the original entry again.
This descriptor is inert data: only the current Activity transition may install
it. Successful decoding/checking does not prove native predecessor provenance.
-/
import Compiler.BendActivityOrigin
import Compiler.BendActivityProgram
import Compiler.BendRunCore
import Theory.BendClosureDecode
import Theory.BendClosureDenotation
import Theory.BendClosureReification
import Theory.BendClosureResponse

namespace Minidregg.Compiler.BendActivitySegment
open Minidregg.Theory
open BendTT BendClosureArena BendClosureMachine
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.BendClosureContinuationCodec
set_option autoImplicit false

structure Signature (core : BendCoreAdmission.Checked) (pin : TypePin) where
  selected : BendCoreAdmission.Entry core
  nameExact : selected.name = pin.definition
  bytesExact : typeBytes selected.definition.T = pin.typeBytes
  resultFamily : Term
  typeExact : selected.definition.T = .All .Q1 BendClosureResponse.responseType resultFamily

/-- Re-read the exact source Book and compare canonical full type bytes. -/
def signature (core : BendCoreAdmission.Checked) (pin : TypePin) :
    Option (Signature core pin) := do
  let .ok selected := BendCoreAdmission.entry core pin.definition | none
  if nameExact : selected.name = pin.definition then
    if bytesExact : typeBytes selected.definition.T = pin.typeBytes then
      match shape : selected.definition.T with
      | .All .Q1 domain family =>
          if domainExact : domain = BendClosureResponse.responseType then
            some ⟨selected,nameExact,bytesExact,family,by simpa [domainExact] using shape⟩
          else none
      | _ => none
    else none
  else none

/-- Heap origin reification names both immutable pointers. It never mistakes a
later residual focus for the term at which this pure source segment began. -/
structure ResponseSource (program : Program) (heap : Heap) (origin : ResponseOrigin) where
  continuation : Term
  continuationExact : Denotes program heap origin.continuation continuation
  inputExact : Denotes program heap origin.input (BendClosureResponse.responseTerm origin.bit)

def ResponseSource.initial {program : Program} {heap : Heap} {origin : ResponseOrigin}
    (source : ResponseSource program heap origin) : Term :=
  .App .Q1 source.continuation (BendClosureResponse.responseTerm origin.bit)

def responseSource (program : Program) (heap : Heap) (ticks : Nat)
    (origin : ResponseOrigin) : Option (ResponseSource program heap origin) := do
  let continuation ← decode program heap ticks origin.continuation
  let input ← decode program heap ticks origin.input
  if exact : input.term = BendClosureResponse.responseTerm origin.bit then
    some ⟨continuation.term,continuation.exact,by rw [← exact]; exact input.exact⟩
  else none

/-- Append-only allocation preserves the original source application, including
captured Q0 terms. This says nothing about authorization to consume the origin. -/
def ResponseSource.extend {program : Program} {before after : Heap}
    {origin : ResponseOrigin} (source : ResponseSource program before origin)
    (extension : Extends before after) : ResponseSource program after origin :=
  ⟨source.continuation,source.continuationExact.extends extension,
    source.inputExact.extends extension⟩

theorem ResponseSource.extend_initial {program : Program} {before after : Heap}
    {origin : ResponseOrigin} (source : ResponseSource program before origin)
    (extension : Extends before after) :
    (source.extend extension).initial = source.initial := rfl

theorem ResponseSource.unique {program : Program} {heap : Heap} {origin : ResponseOrigin}
    (left right : ResponseSource program heap origin) : left.initial = right.initial := by
  unfold ResponseSource.initial
  rw [left.continuationExact.functional right.continuationExact]

structure Checked {source : BendActivityProgram.Source}
    (prepared : BendActivityProgram.Prepared source) (heap : Heap) (origin : Origin) where
  initial : Term
  outputType : Term
  admission : BendInvocationAdmission.Admission prepared.core.book initial outputType
  originExact : match origin with
    | none => initial = .Ref source.entry ∧ outputType = prepared.entry.definition.T
    | some response => ∃ decoded : ResponseSource prepared.compiled.library.program heap response,
        ∃ selected : Signature prepared.core response.signature,
          initial = decoded.initial ∧
          outputType = Term.inst selected.resultFamily (BendClosureResponse.responseTerm response.bit)

/-- Actual source typing/closedness/liveness is rechecked for the exact resumed
application. The result type is dependent instantiation, not a caller-selected
schema. The native Activity gate must bind origin to the consumed predecessor. -/
def check {source : BendActivityProgram.Source}
    (prepared : BendActivityProgram.Prepared source) (heap : Heap)
    (origin : Origin) (decodeTicks checkerTicks : Nat) :
    Option (Checked prepared heap origin) :=
  match origin with
  | none => some ⟨.Ref source.entry,prepared.entry.definition.T,prepared.admitted,rfl,rfl⟩
  | some response => do
      let decoded ← responseSource prepared.compiled.library.program heap decodeTicks response
      let selected ← signature prepared.core response.signature
      let output := Term.inst selected.resultFamily (BendClosureResponse.responseTerm response.bit)
      let admission ← BendInvocationAdmission.admit prepared.core.book checkerTicks decoded.initial output
      some ⟨decoded.initial,output,admission,decoded,selected,rfl,rfl⟩

/-- The existing exact source evaluator consumes this origin, rather than
silently restarting the original entry after an external response. -/
def runChecked {source : BendActivityProgram.Source}
    {prepared : BendActivityProgram.Prepared source} {heap : Heap} {origin : Origin}
    (checked : Checked prepared heap origin) (limits : BendRunCore.Limits) :
    Except BendRunCore.Refusal (BendRunCore.Checked prepared.core checked.initial checked.outputType limits) :=
  BendRunCore.check prepared.core checked.initial checked.outputType limits

#assert_axioms signature
#assert_axioms responseSource
#assert_axioms ResponseSource.extend_initial
#assert_axioms ResponseSource.unique
#assert_axioms check
#assert_axioms runChecked
end Minidregg.Compiler.BendActivitySegment
