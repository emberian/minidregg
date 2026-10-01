/-
# Kernel.NockProgramCell — the program cell's reads (host ops 131–133)

The sample itself is `Kernel.NockProgramCell.Sample`. The reads (`checkProgram`,
`sampleFor`) are what host ops 131 and 133 serve. The WRITE is the ordinary resource
birth (`storage: "nock"`).
-/
import Kernel.NockProgramCell.Sample
import Compiler.CanonicalCellRegistry

namespace Minidregg.Kernel.NockProgramCell

open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.NockProgramCodec

set_option autoImplicit false

/-! ## Reads served to the client (ops 131–133) -/

/-- Op 131: what a birth of these bytes would meet, against the live store. -/
inductive CheckVerdict where
  | malformed
  | refused (reason : Refusal)
  | admissible (program : Program) (id : Digest) (code : Digest) (cellId : Nat) (present : Bool)

/-- Op 131 on this deployment (`disabled`: what its operator disabled): the record's
evaluator resolves and admits it (`Evaluator.admitRecord`: `unknownEvaluator`,
`evaluatorDisabled`, then the evaluator's own `admit`), then its libraries are present. -/
def checkProgram (disabled : List Digest) (domain : Digest)
    (directory : Directory Nat CanonicalCellRegistry.registry) (program : Program) : CheckVerdict :=
  match Evaluator.admitRecord disabled program with
  | .error reason => .refused reason
  | .ok () =>
    if CanonicalCellRegistry.librariesPresent domain directory program then
      let id := programId program
      .admissible program id (codeDigest program.jam)
        (CanonicalCellRegistry.programCellId domain program)
        (CanonicalCellRegistry.loadProgram domain directory id).isSome
    else .refused .missingLibrary

/-- Op 133: the canonical sample bytes for a stored program, on its evaluator. `values` are
`(target index, slot, value)` triples; a duplicate `(index, slot)` refuses. -/
inductive SampleVerdict where
  | missingProgram
  /-- The program's evaluator does not resolve here (unknown, or disabled). -/
  | unresolved (reason : Evaluator.Unresolved)
  | ambiguousValues
  | refused
  | sample (jam : List UInt8)

def readOf (values : List (Nat × String × Int)) (i : Nat) (slot : String) : Option Int :=
  (values.find? fun v => v.1 = i ∧ v.2.1 = slot).map fun v => v.2.2

def sampleFor (disabled : List Digest) (domain : Digest)
    (directory : Directory Nat CanonicalCellRegistry.registry)
    (id : Digest) (ctx : Context) (targets : List Nat) (values : List (Nat × String × Int)) :
    SampleVerdict :=
  match CanonicalCellRegistry.loadProgram domain directory id with
  | none => .missingProgram
  | some program =>
    match Evaluator.resolve disabled program.evaluator with
    | .error reason => .unresolved reason
    | .ok E =>
      if (values.map fun v => (v.1, v.2.1)).Nodup then
        match E.sampleOf program.abi ctx targets (readOf values) with
        | none => .refused
        | some input => .sample (E.encodeInput input)
      else .ambiguousValues

end Minidregg.Kernel.NockProgramCell
