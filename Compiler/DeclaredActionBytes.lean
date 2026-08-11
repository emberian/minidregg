/-
# Compiler.DeclaredActionBytes -- fail-closed bytes for declared action batches

The compiler boundary decodes the lawful first-order declaration codec and
checks its pinned schema version.  Acceptance retains the literal decode
equality; downstream code consumes that declaration directly.  There is no
host callback and no independently supplied effect digest, patch, nullifier,
authority target, or charge.
-/
import Theory.DeclaredActionLowering

namespace Minidregg.Compiler.DeclaredActionBytes

open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.DeclaredActionLowering

set_option autoImplicit false

inductive RejectReason
  | malformed
  | schemaVersion (expected actual : Nat)
  | emptyBatch
  deriving DecidableEq, Repr

/-- Proof-relevant accepted artifact.  `accepted_source_decoded` below binds
the exact source bytes to the declaration used by every later projection. -/
structure Compiled {kind : ResourceKind} (target : ResourceId kind)
    (expectedVersion : Nat) where
  declaration : Declaration target
  schemaVersionExact : declaration.schemaVersion = expectedVersion
  actionsPresent : declaration.actions ≠ []

inductive Outcome {kind : ResourceKind} (target : ResourceId kind)
    (expectedVersion : Nat)
  | accepted (compiled : Compiled target expectedVersion)
  | rejected (reason : RejectReason)

/-- Ordered fail-closed compilation.  Only the lawful decoder constructs a
declaration, and the accepted value is that exact decoded declaration. -/
def compile {kind : ResourceKind} (target : ResourceId kind)
    (expectedVersion : Nat) (source : List UInt8) :
    Outcome target expectedVersion :=
  match (declarationCodec target).decode source with
  | none => .rejected .malformed
  | some declaration =>
      if version : declaration.schemaVersion = expectedVersion then
        if actions : declaration.actions = [] then
          .rejected .emptyBatch
        else
          .accepted
            { declaration := declaration
              schemaVersionExact := version
              actionsPresent := actions }
      else .rejected (.schemaVersion expectedVersion declaration.schemaVersion)

/-- Canonical encoder output compiles to the original nonempty declaration. -/
theorem compile_encode_accepted {kind : ResourceKind}
    {target : ResourceId kind} (declaration : Declaration target)
    (actions : declaration.actions ≠ []) :
    compile target declaration.schemaVersion
        ((declarationCodec target).encode declaration) =
      .accepted
        { declaration := declaration
          schemaVersionExact := rfl
          actionsPresent := actions } := by
  simp [compile, (declarationCodec target).decode_encode declaration, actions]

/-- Every accepted artifact is exactly the declaration decoded from the input
bytes.  This is the retained compiler invariant, stated without storing a
second copy of the bytes or an interpreter function in the artifact. -/
theorem accepted_source_decoded {kind : ResourceKind}
    {target : ResourceId kind} {expectedVersion : Nat} {source : List UInt8}
    {compiled : Compiled target expectedVersion}
    (accepted : compile target expectedVersion source = .accepted compiled) :
    (declarationCodec target).decode source = some compiled.declaration := by
  unfold compile at accepted
  cases decoded : (declarationCodec target).decode source with
  | none => simp [decoded] at accepted
  | some declaration =>
      simp only [decoded] at accepted
      split at accepted
      · split at accepted
        · simp at accepted
        · cases accepted
          simpa using decoded
      · simp at accepted

/-- Changing any byte away from canonical unary zero is malformed.  This
tooth prevents same-length noncanonical byte aliases at the compiler edge. -/
theorem nonzero_byte_rejected {kind : ResourceKind}
    (target : ResourceId kind) (expectedVersion : Nat)
    (before after : List UInt8) (byte : UInt8) (nonzero : byte ≠ 0) :
    compile target expectedVersion (before ++ byte :: after) =
      .rejected .malformed := by
  have notAll : ¬ ∀ candidate ∈ before ++ byte :: after, candidate = 0 := by
    intro allZero
    exact nonzero (allZero byte (by simp))
  have allFalse :
      (before ++ byte :: after).all (fun candidate => candidate == 0) = false := by
    apply Bool.eq_false_iff.mpr
    intro allTrue
    apply notAll
    simpa only [List.all_eq_true, beq_iff_eq] using allTrue
  have decodedNone :
      (declarationCodec target).decode (before ++ byte :: after) = none := by
    change (if (before ++ byte :: after).all (fun candidate => candidate == 0)
        then declarationOfCode target ((before ++ byte :: after).length - 1)
        else none) = none
    rw [allFalse]
    rfl
  simp [compile, decodedNone]

end Minidregg.Compiler.DeclaredActionBytes
