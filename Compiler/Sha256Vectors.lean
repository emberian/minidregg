/- FIPS 180-4 / NIST CAVP known-answer vectors for `Compiler.Sha256`. -/
import Compiler.Sha256
import Theory.AssertCompiled
namespace Minidregg.Compiler.Sha256
set_option autoImplicit false

theorem empty_vector : hexString "" = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" := by
  native_decide
theorem abc_vector : hexString "abc" = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" := by
  native_decide
/-- Two-block message (FIPS 180-4 example). -/
theorem two_block_vector :
    hexString "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" =
      "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1" := by
  native_decide
/-- 55 and 56 bytes straddle the padding boundary (one block versus two). -/
theorem boundary_vectors :
    hexString (String.ofList (List.replicate 55 'a')) =
      "9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318" ∧
    hexString (String.ofList (List.replicate 56 'a')) =
      "b35439a4ac6f0948b6d6f9e3c6af0f5f590ce20f1bde7090ef7970686ec6738a" := by
  native_decide

#assert_compiled empty_vector
#assert_compiled abc_vector
#assert_compiled two_block_vector
#assert_compiled boundary_vectors
end Minidregg.Compiler.Sha256
