import Compiler.BendProofCshakeBounded
import Theory.AssertCompiled
namespace Minidregg.Compiler.BendProofCshakeBoundedChecks
open BendProofCshakeBounded

def domain : List UInt8 := "DREGG.BEND.PRIVATE-LENGTH/v1".toUTF8.toList

theorem empty_same_capacity : (network domain 136).evaluate (input 136 []) =
    some (#[true] ++ BendProofCshake.bits (Sp800185Cshake256.cshake256Bytes domain [])) := by native_decide

theorem boundary_same_capacity :
    (network domain 136).evaluate (input 136 (List.replicate 135 0xa5)) =
    some (#[true] ++ BendProofCshake.bits
      (Sp800185Cshake256.cshake256Bytes domain (List.replicate 135 0xa5))) := by native_decide

theorem full_same_capacity :
    (network domain 136).evaluate (input 136 (List.replicate 136 0x5a)) =
    some (#[true] ++ BendProofCshake.bits
      (Sp800185Cshake256.cshake256Bytes domain (List.replicate 136 0x5a))) := by native_decide

theorem invalid_length_refuses :
    ((network [] 2).evaluate (Array.replicate 19 false)).map (fun result => result[0]?.getD true) =
      some false := by native_decide

theorem public_prefix_constants :
    (networkPublicPrefix domain 136).evaluate (input 136 (List.replicate 136 0x5a)) =
      (network domain 136).evaluate (input 136 (List.replicate 136 0x5a)) := by native_decide

#assert_compiled public_prefix_constants
#assert_compiled empty_same_capacity
#assert_compiled boundary_same_capacity
#assert_compiled full_same_capacity
#assert_compiled invalid_length_refuses
end Minidregg.Compiler.BendProofCshakeBoundedChecks
