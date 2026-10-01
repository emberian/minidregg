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

def checkProgram (domain : Digest) (directory : Directory Nat CanonicalCellRegistry.registry)
    (program : Program) : CheckVerdict :=
  match check program with
  | .error reason => .refused reason
  | .ok () =>
    if CanonicalCellRegistry.librariesPresent domain directory program then
      let id := programId program
      .admissible program id (codeDigest program.jam)
        (CanonicalCellRegistry.programCellId domain program)
        (CanonicalCellRegistry.loadProgram domain directory id).isSome
    else .refused .missingLibrary

/-- Op 133: the canonical sample jam for a stored program. `values` are
`(target index, slot, value)` triples; a duplicate `(index, slot)` refuses. -/
inductive SampleVerdict where
  | missingProgram
  | ambiguousValues
  | refused
  | sample (jam : List UInt8)

def readOf (values : List (Nat × String × Int)) (i : Nat) (slot : String) : Option Int :=
  (values.find? fun v => v.1 = i ∧ v.2.1 = slot).map fun v => v.2.2

def sampleFor (domain : Digest) (directory : Directory Nat CanonicalCellRegistry.registry)
    (id : Digest) (ctx : Context) (targets : List Nat) (values : List (Nat × String × Int)) :
    SampleVerdict :=
  match CanonicalCellRegistry.loadProgram domain directory id with
  | none => .missingProgram
  | some program =>
    if (values.map fun v => (v.1, v.2.1)).Nodup then
      match sampleOf program.abi ctx targets (readOf values) with
      | none => .refused
      | some noun => .sample (Noun.jam noun)
    else .ambiguousValues

end Minidregg.Kernel.NockProgramCell
