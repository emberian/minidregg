/- One canonical statement shared by source methods, backend plans and results.
It is a byte codec, not an authority or a cryptographic proof. Public proof
inputs must encode these bytes injectively in their target field. -/
import Compiler.BendWorldPlan

namespace Minidregg.Compiler.BendInvocation
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

structure ProgramIdentity where
  semantic : Digest
  artifact : Digest
  program : Digest
  method : Digest
  plan : Digest
  deriving DecidableEq, Repr

structure ExecutionIdentity where
  invocation : Digest
  predecessor : Digest
  authority : Digest
  inputs : List Digest
  tariff : Digest
  /-- Ten lanes in ResourceCost.Lane order. This declaration is not funded
  admission, nor permission to change an existing accepted intent's charge. -/
  capacity : List Nat
  parameters : Digest
  transformer : Digest
  deriving DecidableEq, Repr

structure Result where
  definition : ProgramIdentity
  execution : ExecutionIdentity
  /-- Complete ordered native payloads, never scalar effect summaries. -/
  effects : List BendWorldPlan.Effect
  result : BendWorldPlan.ReturnSlot
  deriving DecidableEq, Repr

def programStream : StreamCodec ProgramIdentity :=
  StreamCodec.xmap (StreamCodec.product digestStream
    (StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product digestStream digestStream))))
    (fun p => (p.semantic, p.artifact, p.program, p.method, p.plan))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩)
    (by intro p; cases p; rfl)

def executionStream : StreamCodec ExecutionIdentity :=
  StreamCodec.xmap (StreamCodec.product digestStream
    (StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product (StreamCodec.list digestStream)
    (StreamCodec.product digestStream (StreamCodec.product (StreamCodec.list StreamCodec.nat)
    (StreamCodec.product digestStream digestStream)))))))
    (fun e => (e.invocation, e.predecessor, e.authority, e.inputs, e.tariff,
      e.capacity, e.parameters, e.transformer))
    (fun e => ⟨e.1, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2.1,
      e.2.2.2.2.2.1, e.2.2.2.2.2.2.1, e.2.2.2.2.2.2.2⟩)
    (by intro e; cases e; rfl)

def resultStream : StreamCodec Result :=
  StreamCodec.xmap (StreamCodec.product programStream
    (StreamCodec.product executionStream
    (StreamCodec.product (StreamCodec.list BendWorldPlan.effectStream)
      BendWorldPlan.returnStream)))
    (fun r => (r.definition, r.execution, r.effects, r.result))
    (fun r => ⟨r.1, r.2.1, r.2.2.1, r.2.2.2⟩)
    (by intro r; cases r; rfl)

def frame : List UInt8 := "DREGG/BEND/BOUND-RESULT/v1".toUTF8.toList
def encode (r : Result) : List UInt8 := frame ++ resultStream.encode r
def decode (bytes : List UInt8) : Option Result :=
  NockProgramCodec.framedDecode frame resultStream bytes
def resultId (r : Result) : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.BOUND-RESULT/v1".toUTF8.toList (encode r)).digest

/-- Both authored selector and emitted core entry survive specialization. The
resolution/elaboration correspondence remains a separate checked certificate. -/
def methodId (a : BendWorldProgramCodec.Artifact) : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.METHOD/v1".toUTF8.toList
    ((StreamCodec.product digestStream
      (StreamCodec.product StreamCodec.nat
      (StreamCodec.product PolicyRecordCodec.stringStream
      (StreamCodec.product PolicyRecordCodec.stringStream digestStream)))).encode
      (BendWorldSource.packageId a.source, a.source.entryModule,
        a.source.entryDefinition, a.entry, a.plan))).digest

def matchesArtifact (r : Result) (a : BendWorldProgramCodec.Artifact) : Bool :=
  decide (r.definition.semantic = BendWorldProgramCodec.semanticId a ∧
    r.definition.artifact = BendWorldProgramCodec.artifactId a ∧
    r.definition.program = BendWorldProgramCodec.executionProgramId a ∧
    r.definition.method = methodId a ∧ r.definition.plan = a.plan ∧
    r.execution.tariff = a.profile.charge ∧
    r.execution.capacity.length = 10)

theorem exact_artifact {r : Result} {a : BendWorldProgramCodec.Artifact}
    (h : matchesArtifact r a = true) :
    r.definition.semantic = BendWorldProgramCodec.semanticId a ∧
    r.definition.artifact = BendWorldProgramCodec.artifactId a ∧
    r.definition.program = BendWorldProgramCodec.executionProgramId a ∧
    r.definition.method = methodId a ∧ r.definition.plan = a.plan ∧
    r.execution.tariff = a.profile.charge ∧
    r.execution.capacity.length = 10 := by
  simpa only [matchesArtifact, decide_eq_true_eq] using h

theorem roundtrip (r : Result) : decode (encode r) = some r :=
  NockProgramCodec.framedDecode_encode frame resultStream r
theorem canonical {bytes : List UInt8} {r : Result}
    (h : decode bytes = some r) : encode r = bytes :=
  NockProgramCodec.framedDecode_canonical h

end Minidregg.Compiler.BendInvocation
