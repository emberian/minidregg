import Compiler.BendCommittedNetwork
import Theory.AssertCompiled

/- Inhabited executable shared-wire consumer. The tiny execution computes XOR
of two input bytes. Its output bits are the canonical payload byte fed to the
real Context/salt/length framer and cSHAKE circuit. This is a composition test,
not an assertion that this byte operation is a world-admitted Bend method. -/
namespace Minidregg.Compiler.BendCommittedNetworkChecks
open Minidregg.Theory TypedAuthorization
open ObjectiveProofContext ObliviousNetwork BendCommittedNetwork

def context : Context :=
  ⟨.privateEffects, ⟨⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩⟩, ⟨6⟩, ⟨7⟩, 8,
    ⟨9⟩, ⟨10⟩, ⟨11⟩, [64]⟩

def execution : Network where
  inputCount := 16
  gates := (Array.range 8).map (fun i => .xor i (8 + i))
  outputs := (Array.range 8).map (· + 16)

def salt : List UInt8 := List.replicate 32 0x5a

def domain : String := "DREGG.BEND.INPUT-COMMIT/v1"

def actual (left right : UInt8) : Option (Array Bool) := do
  let prepared ← prepare execution domain context 1 execution.outputs
  prepared.candidate.whole.evaluate
    (BendProofCshake.bits [left, right] ++ BendProofCshake.bits salt ++ #[false, true])

def expected (left right : UInt8) : Array Bool :=
  BendProofCshake.bits [left ^^^ right] ++ #[true] ++
    BendProofCshake.bits (Sp800185Cshake256.cshake256Bytes domain.toUTF8.toList
      (BendCommitmentFrame.frameBytes context salt [left ^^^ right]))

theorem source_output_and_commitment : actual 0x37 0xa5 = some (expected 0x37 0xa5) := by native_decide

theorem different_execution_input : actual 0x36 0xa5 = some (expected 0x36 0xa5) := by native_decide

theorem invalid_payload_map_refuses :
    (prepare execution domain context 1 #[999]).isNone = true := by native_decide

#assert_compiled source_output_and_commitment
#assert_compiled different_execution_input
#assert_compiled invalid_payload_map_refuses
end Minidregg.Compiler.BendCommittedNetworkChecks
