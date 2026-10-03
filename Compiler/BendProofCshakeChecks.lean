import Compiler.BendProofCshake
import Theory.AssertCompiled
namespace Minidregg.Compiler.BendProofCshakeChecks
open BendProofCshake

theorem empty_shake : (network [] 0).evaluate #[] =
    some (bits (Sp800185Cshake256.cshake256Bytes [] [])) := by native_decide

def domain : List UInt8 := "DREGG.BEND.COMMITMENT-CIRCUIT/v1".toUTF8.toList

theorem last_byte_padding :
    (network domain 135).evaluate (bits (List.replicate 135 0xa5)) =
      some (bits (Sp800185Cshake256.cshake256Bytes domain (List.replicate 135 0xa5))) := by native_decide

theorem extra_block_padding :
    (network domain 136).evaluate (bits (List.replicate 136 0x5a)) =
      some (bits (Sp800185Cshake256.cshake256Bytes domain (List.replicate 136 0x5a))) := by native_decide

#assert_compiled empty_shake
#assert_compiled last_byte_padding
#assert_compiled extra_block_padding
end Minidregg.Compiler.BendProofCshakeChecks
