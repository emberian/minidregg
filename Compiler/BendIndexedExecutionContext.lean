/- Exact edition-and-table retention for optimized Bend continuations.
This reuses the existing canonical full-context codec and restoration guard.
It supplies no authority, source cost, or backend faithfulness assumption.
-/
import Compiler.BendClosureCompileIndexed
import Compiler.BendClosureContinuationCodec

namespace Minidregg.Compiler.BendIndexedExecutionContext
open Minidregg.Theory BendTT BendClosureArena BendClosureMachine
open BendClosureContinuationCodec
set_option autoImplicit false

/-- Compiler edition has its own delimiter before source/native binding bytes.
Old contexts remain usable by their explicit old receiver; this receiver never
silently relocates old code pointers into a newly shared code table. -/
def compilerFrame : List UInt8 :=
  "DREGG.BEND.COMPILED/".toUTF8.toList ++ BendClosureCompileIndexed.edition.toUTF8.toList ++ [0]

def context (bindingBytes : List UInt8) (limits : Limits) (library : Library) :
    ExecutionContext := executionContext (compilerFrame ++ bindingBytes) limits library

def bytes (bindingBytes : List UInt8) (limits : Limits) (library : Library) : List UInt8 :=
  encodeContext (context bindingBytes limits library)

/-- Exact arrays and bounds remain in the canonical identity, not just the
compiler tag or a source digest. The native binding stays a receiving premise. -/
theorem exact_context {leftBinding rightBinding : List UInt8} {leftLimits rightLimits : Limits}
    {leftLibrary rightLibrary : Library}
    (same : bytes leftBinding leftLimits leftLibrary = bytes rightBinding rightLimits rightLibrary) :
    context leftBinding leftLimits leftLibrary = context rightBinding rightLimits rightLibrary :=
  context_bytes_injective same

private theorem frame_nonempty : 0 < compilerFrame.length := by
  simp only [compilerFrame, List.length_append, List.length_cons, List.length_nil]
  omega

/-- The legacy and optimized identities differ even if one tiny source happens
not to benefit from sharing and produces equal operational tables. -/
theorem legacy_context_different (bindingBytes : List UInt8) (limits : Limits) (library : Library) :
    encodeContext (executionContext bindingBytes limits library) ≠ bytes bindingBytes limits library := by
  intro same
  have exact := context_bytes_injective same
  have first := congrArg Prod.fst exact
  have length := congrArg List.length first
  simp only [context, executionContext, List.length_append] at length
  have nonempty := frame_nonempty
  omega

/-- Reject a canonical historical checkpoint under the new expected identity.
The checkpoint remains intact and can still be retained/handled by its explicit
historical receiver. Neither table relocation nor a new profile is inferred. -/
theorem legacy_checkpoint_refused (bindingBytes : List UInt8) (limits : Limits) (library : Library)
    (maximumBytes generation : Nat) (state : State) :
    restore maximumBytes (bytes bindingBytes limits library) generation
      (encode ⟨encodeContext (executionContext bindingBytes limits library), generation, state⟩) = none := by
  simp [restore, legacy_context_different bindingBytes limits library]

/-- The new identity uses the existing full-state exact pause/resume theorem;
source count/public fee accounting remains the caller's unchanged contract. -/
theorem serialized_resume_exact (bindingBytes : List UInt8) (limits : Limits) (library : Library)
    (generation first second : Nat) (initial : State) (maximumBytes : Nat)
    (fits : (encode ⟨bytes bindingBytes limits library, generation,
      run limits library first initial⟩).length ≤ maximumBytes) :
    (restore maximumBytes (bytes bindingBytes limits library) generation
      (encode ⟨bytes bindingBytes limits library, generation, run limits library first initial⟩)).map
      (run limits library second) = some (run limits library (first + second) initial) :=
  BendClosureContinuationCodec.serialized_resume_exact limits library
    (bytes bindingBytes limits library) generation first second initial maximumBytes fits

#assert_axioms exact_context
#assert_axioms legacy_context_different
#assert_axioms legacy_checkpoint_refused
#assert_axioms serialized_resume_exact
end Minidregg.Compiler.BendIndexedExecutionContext
