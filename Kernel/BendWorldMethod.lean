/- Source inspection for accepted native methods. A provenance link names the
actual immutable executable record and keeps the complete native Trace. It
does not assert source/compiler equivalence or admit any additional evaluator. -/
import Compiler.BendWorldProgramCodec
import Kernel.WorldMethodTrace

namespace Minidregg.Kernel.BendWorldMethod
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.DurableDataIntent
set_option autoImplicit false

structure SourceLink where
  artifact : BendWorldProgramCodec.Artifact
  trace : WorldMethodTrace.Trace
  checked : CheckedRun
  runExact : trace.run = some checked
  programExact : checked.claim.programId = BendWorldProgramCodec.executionProgramId artifact
  evaluatorExact : checked.evaluator = artifact.program.evaluator
  profileExact : artifact.program.evaluator = artifact.profile.evaluator
  formed : BendWorldProgramCodec.wellFormed artifact = true

/-- Only link the exact checked native method. Absent runs, wrong executable or
evaluator, and malformed sealed artifacts fail closed. Authorization still
belongs to the controller that produced the accepted Trace. -/
def link (artifact : BendWorldProgramCodec.Artifact) (trace : WorldMethodTrace.Trace) :
    Option SourceLink :=
  match exact : trace.run with
  | none => none
  | some checked =>
    if program : checked.claim.programId = BendWorldProgramCodec.executionProgramId artifact then
      if evaluator : checked.evaluator = artifact.program.evaluator then
        if profile : artifact.program.evaluator = artifact.profile.evaluator then
          if formed : BendWorldProgramCodec.wellFormed artifact = true then
            some ⟨artifact, trace, checked, exact, program, evaluator, profile, formed⟩
          else none
        else none
      else none
    else none

/-- Receiving-path entry: derive the trace from the actual accepted invocation.
The generic `link` above is only a provenance utility, not an admission check. -/
def ofAccepted {F : Type} [Field F] [DecidableEq F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {command : Command}
    (artifact : BendWorldProgramCodec.Artifact)
    (prepared : PreparedInvocation deployment profile ambient durable command)
    {signed : SignedCommand}
    (accepted : DeclaredResourceController.AcceptedInvocation prepared signed) :
    Option SourceLink :=
  link artifact (WorldMethodTrace.ofAccepted prepared accepted)

theorem complete_trace_retained (source : SourceLink) :
    source.trace.run = some source.checked := source.runExact

theorem exact_program_retained (source : SourceLink) :
    source.checked.claim.programId =
      NockProgramCodec.programId source.artifact.program := source.programExact

end Minidregg.Kernel.BendWorldMethod
