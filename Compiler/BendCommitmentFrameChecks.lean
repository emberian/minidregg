import Compiler.BendCommitmentFrame
import Theory.AssertCompiled
namespace Minidregg.Compiler.BendCommitmentFrameChecks
open Minidregg.Theory Tower256ConcreteBackend BendCommitmentFrame

def publicContext : List UInt8 := [3, 5, 255]
def salt : List UInt8 := List.replicate 32 0xa5

def input (payload : List UInt8) : Array Bool :=
  BendProofCshake.bits salt ++ BendProofCshakeBounded.input 4 payload

def expected (payload : List UInt8) : Array Bool :=
  let frame := publicContext ++ bytesStream.encode salt ++ bytesStream.encode payload
  let capacity := frameCapacity publicContext 4
  #[true] ++ BendProofCshakeBounded.input capacity frame

theorem empty_payload : (frameNetwork publicContext 4).evaluate (input []) =
    some (expected []) := by native_decide

theorem private_payload : (frameNetwork publicContext 4).evaluate (input [7, 8]) =
    some (expected [7, 8]) := by native_decide

theorem many_hot_refuses :
    ((frameNetwork publicContext 4).evaluate
      ((input []).setIfInBounds ((32 + 4) * 8 + 2) true)).map
        (fun output => output[0]?.getD true) = some false := by native_decide

#assert_compiled empty_payload
#assert_compiled private_payload
#assert_compiled many_hot_refuses
end Minidregg.Compiler.BendCommitmentFrameChecks
