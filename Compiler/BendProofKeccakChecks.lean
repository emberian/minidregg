import Compiler.BendProofKeccak
import Theory.AssertCompiled

/- Finite executable conformance checks, explicitly compiler-trusted. These
are falsifiers for indexing/rotation/round integration, not the missing general
permutation or cSHAKE commitment refinement theorem. -/
namespace Minidregg.Compiler.BendProofKeccakChecks
open BendProofKeccak
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def encodeState (state : Sp800185Cshake256.State) : Array Bool :=
  (Array.ofFn fun lane : Fin 25 => Array.ofFn fun bit : Fin 64 =>
    (state.getD lane.val Sp800185Cshake256.zeroLane).getLsbD bit.val).flatten

def patternState : Sp800185Cshake256.State :=
  Array.ofFn fun lane : Fin 25 =>
    BitVec.ofNat 64 ((lane.val + 1) * 0x0102040810204081)

theorem network_valid : network.valid = true := by native_decide

theorem zero_state_conformance :
    network.evaluate (encodeState Sp800185Cshake256.zeroState) =
      some (encodeState (Sp800185Cshake256.keccakF1600 Sp800185Cshake256.zeroState)) := by
  native_decide

theorem patterned_state_conformance :
    network.evaluate (encodeState patternState) =
      some (encodeState (Sp800185Cshake256.keccakF1600 patternState)) := by
  native_decide

#assert_compiled network_valid
#assert_compiled zero_state_conformance
#assert_compiled patterned_state_conformance
end Minidregg.Compiler.BendProofKeccakChecks
