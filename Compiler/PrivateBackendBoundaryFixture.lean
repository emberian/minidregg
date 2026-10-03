import Compiler.PrivateAllocationReceipt
namespace Minidregg.Compiler.PrivateBackendBoundaryFixture
open Minidregg.Kernel.PrivateSuccessorCustody
open Minidregg.Compiler.PrivateSuccessorCustodyCodec
open Minidregg.Compiler.PrivateBackendBoundary
open Minidregg.Theory.TypedAuthorization

def generation : GenerationKey :=
  ⟨⟨2^255 + 42⟩, "signed.command".toUTF8.toList, 3, 255, ⟨2^256 - 1⟩⟩
def row : CorrelationId := ⟨⟨2^255 + 12345⟩, 254⟩
def request : ReservationRequest := ⟨row, generation, .holderOutputPad⟩
def allocated : Journal :=
  ⟨[row], [⟨row, generation, .holderOutputPad, .reserved⟩]⟩

theorem fixture_is_native_reserve :
    reserve Journal.empty row generation .holderOutputPad = some allocated := by
  rfl
#assert_axioms fixture_is_native_reserve

def printBytes (bytes : List UInt8) : IO Unit :=
  IO.println ("[" ++ String.intercalate "," (bytes.map fun b => toString b.toNat) ++ "]")

def main : IO Unit := do
  printBytes (encodeJournal Journal.empty)
  printBytes (requestStream.encode request)
  printBytes (encodeJournal allocated)
  printBytes (Minidregg.Compiler.PrivateAllocationReceipt.receiptStream.encode
    ⟨requestStream.encode request, [9,8,7], encodeJournal allocated, List.replicate 32 6⟩)
end Minidregg.Compiler.PrivateBackendBoundaryFixture

def main := Minidregg.Compiler.PrivateBackendBoundaryFixture.main
