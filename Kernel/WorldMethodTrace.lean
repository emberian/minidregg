/- Native method dependency/effect contract. The trace is made from the actual
accepted invocation, not supplied by a caller or inferred from a method name.
The complete authenticated preimage, current read guards, pending writes and
exact metered run travel together into private lowering/agreement consumers. -/
import Kernel.DeclaredResourceController
import Theory.AssertAxioms

namespace Minidregg.Kernel.WorldMethodTrace

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

/-- Typed native effect requests retain their actual source payload, including
content edits, stream messages and canonical definitions. Their resulting posts
are obtained through ordinary native computation and admission. -/
structure Participant where
  index : Nat
  cell : Nat
  expectedRoot : Digest
  payload : Payload
  /-- Complete canonical preimage; missing values are not replaced with zero. -/
  preimage : List UInt8
  projection : List (String × Int)

structure Trace where
  candidate : Digest
  commandBytes : List UInt8
  subject : SubjectId
  participants : List Participant
  /-- Current credential, law, structural kind, clock, budget and audience roots. -/
  readGuards : List ReadGuard
  /-- The exact native successor writes (including charge/nullifier/outbox). -/
  writes : List DataWrite
  run : Option CheckedRun

variable {F : Type} [Field F] [DecidableEq F]
  {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
  {ambient : Ambient} {ground : Ground deployment} {command : Command}

def participant (prepared : PreparedInvocation deployment profile ambient ground command)
    (index : Fin command.targets.length) : Participant :=
  { index := index.val
    cell := command.targets[index].target
    expectedRoot := command.targets[index].expectedTargetRoot
    payload := command.targets[index].payload
    preimage := command.targets[index].materializer.codec.encode (prepared.targets index).pre.logical
    projection := targetProjection command.subject command.targets[index]
      (prepared.targets index).pre.logical (prepared.targets index).pre.logical }

def ofAccepted (prepared : PreparedInvocation deployment profile ambient ground command)
    {signed : SignedCommand} (accepted : AcceptedInvocation prepared signed) : Trace :=
  { candidate := effectsDigest ground.authority.domain profile.semantics command
    commandBytes := commandCodec.encode command
    subject := command.subject
    participants := (List.finRange command.targets.length).map (participant prepared)
    readGuards := accepted.readGuards
    writes := DeclaredResourceController.writes prepared
    run := prepared.run }

/-- A guard discharged by a write is still a dependency: its exact old root is
in the write, rather than being dropped from the footprint. -/
def Protects (trace : Trace) (cell : CellId) (root : Digest) : Prop :=
  (∃ guard ∈ trace.readGuards, guard.cellId = cell ∧ guard.expectedRoot = root) ∨
  (∃ write ∈ trace.writes, write.cellId = cell ∧ write.expectedPre = root)

theorem read_dependency_retained
    (prepared : PreparedInvocation deployment profile ambient ground command)
    {signed : SignedCommand} (accepted : AcceptedInvocation prepared signed)
    (guard : ReadGuard) (present : guard ∈ accepted.readGuards) :
    Protects (ofAccepted prepared accepted) guard.cellId guard.expectedRoot :=
  Or.inl ⟨guard, present, rfl, rfl⟩

theorem write_dependency_retained
    (prepared : PreparedInvocation deployment profile ambient ground command)
    {signed : SignedCommand} (accepted : AcceptedInvocation prepared signed)
    (write : DataWrite) (present : write ∈ DeclaredResourceController.writes prepared) :
    Protects (ofAccepted prepared accepted) write.cellId write.expectedPre :=
  Or.inr ⟨write, present, rfl, rfl⟩

theorem every_participant_retained
    (prepared : PreparedInvocation deployment profile ambient ground command)
    {signed : SignedCommand} (accepted : AcceptedInvocation prepared signed)
    (index : Fin command.targets.length) :
    participant prepared index ∈ (ofAccepted prepared accepted).participants := by
  apply List.mem_map.mpr
  exact ⟨index, List.mem_finRange index, rfl⟩

/-- Trace extraction retains the entire checked run, including native output
bytes, exceptions/termination discipline, evaluator identity and exact count. -/
theorem run_retained
    (prepared : PreparedInvocation deployment profile ambient ground command)
    {signed : SignedCommand} (accepted : AcceptedInvocation prepared signed) :
    (ofAccepted prepared accepted).run = prepared.run := rfl

#assert_axioms read_dependency_retained
#assert_axioms write_dependency_retained
#assert_axioms every_participant_retained
#assert_axioms run_retained

end Minidregg.Kernel.WorldMethodTrace
