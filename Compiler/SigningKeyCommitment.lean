/- Shared source commitment leaf for pre-rotation and paid enrollment memos.
It contains no registry/receiver dependency, so cell codecs can use exactly the
same commitment without importing the receiving runtime back into themselves. -/
import Compiler.Sp800185Cshake256

namespace Minidregg.Compiler.SigningKeyCommitment
open Minidregg.Theory.TypedAuthorization (Digest)
set_option autoImplicit false

def tag : List UInt8 := "DREGG.SIGNING-KEY.NEXT/v1".toUTF8.toList

def digest (publicKey : List UInt8) : Digest :=
  (Sp800185Cshake256.hash tag publicKey).digest

end Minidregg.Compiler.SigningKeyCommitment
