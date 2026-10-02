/-
# Assurance.EvaluatorAudit — concrete evaluator admission checks

Runtime evaluator data, admission decisions, and general theorems stay in
`Compiler.Evaluator`. Both deployed and research proof umbrellas require these
kernel-decided admission fixtures. Their original theorem names and axiom pins
are preserved without placing the fixture proofs in Host's runtime imports.
-/
import Compiler.Evaluator

namespace Minidregg.Compiler

open Minidregg.Theory
open Minidregg.Theory.Eval
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Compiler.NockProgramCodec (Abi SampleSlot OutputSlot Program EffectRefusal
  NamesNulFree AbiShape abiVersion)
open Minidregg.Kernel.NockProgramCell (Context Sample sampleRecord)

set_option autoImplicit false

namespace Evaluator

/-! ## Poles: the NUL rule, decided -/

/-- A one-slot ABI whose slot key is `key`. -/
def nulPoleAbi (key : String) : Abi :=
  { version := abiVersion, fuel := 100, libraries := [], outputs := [],
    sample := [{ target := 0, slot := "f/2", key := key, type := .nat }] }

def nulPoleProgram (key : String) : Program :=
  ⟨⟨0⟩, Noun.jam (Nock.op 0 (.atom 1)), nulPoleAbi key, Kernel.NockEntry.encodeParams ⟨2⟩⟩

/-- Refused: the key `"a\u0000"`. -/
theorem pole_nulInName : refusalOf (Machine.nock.admit (nulPoleProgram "a\u0000")) = some .nulInName := by
  decide +kernel
/-- Admitted: the key `"a"`, with Nock's params decoded to arm 2. -/
theorem pole_nulFree_admitted : (Machine.nock.admit (nulPoleProgram "a")).toOption = some ⟨2⟩ := by
  decide +kernel
/-- Params that do not decode are refused by name. -/
theorem pole_paramsMalformed :
    refusalOf (Machine.nock.admit { nulPoleProgram "a" with params := [1, 2, 3] }) =
      some .paramsMalformed := by decide +kernel

/-- info: 'Minidregg.Compiler.Evaluator.pole_nulInName' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pole_nulInName
/-- info: 'Minidregg.Compiler.Evaluator.pole_nulFree_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pole_nulFree_admitted
/-- info: 'Minidregg.Compiler.Evaluator.pole_paramsMalformed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pole_paramsMalformed
end Evaluator

end Minidregg.Compiler
