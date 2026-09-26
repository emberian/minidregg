import Compiler.FnEvidenceCodec

open Minidregg.Compiler.FnEvidenceCodec
open Minidregg.Compiler.NativeHostCodec

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

def main : IO Unit := do
  let current : Package :=
    ⟨⟨8501⟩, ⟨1⟩, ⟨0⟩, List.replicate 103781 1,
      ⟨⟨101⟩, ⟨102⟩, 2, ⟨103⟩⟩, List.replicate 150000 2⟩
  let bytes ← IO.ofExcept (encodeChecked current)
  let decoded ← IO.ofExcept (decodeChecked bytes)
  require (decoded.originalReceipt == current.originalReceipt &&
    decoded.signedCall.toByteArray == current.signedCall.toByteArray &&
    decoded.acceptedPrefix.toByteArray == current.acceptedPrefix.toByteArray)
    "multi-event current evidence did not round trip"
  require (historicalPackageCodec.decode bytes == none)
    "current frame decoded as historical evidence"
  let historical : Package :=
    ⟨current.domain, current.semantics, current.genesisPin, [1, 2],
      ⟨current.originalReceipt.transactionId, current.originalReceipt.eventId,
        1, current.originalReceipt.imageBoundary⟩, [3, 4]⟩
  let historicalBytes := historicalPackageCodec.encode historical
  require (decodeChecked historicalBytes == .ok historical)
    "historical first-event evidence did not decode"
  require (packageCodec.decode historicalBytes == none)
    "historical frame decoded as current evidence"
  let invalidHistorical : Package :=
    { historical with originalReceipt :=
        { historical.originalReceipt with acceptedCount := 2 } }
  require (match decodeChecked (historicalPackageCodec.encode invalidHistorical) with
    | .error _ => true | .ok _ => false)
    "multi-event package crossed historical frame"
  require (match encodeChecked { current with
      originalReceipt := { current.originalReceipt with acceptedCount := 0 } } with
    | .error _ => true | .ok _ => false)
    "zero accepted count entered current profile"
  IO.println s!"PASS multi-event evidence wire: {bytes.length} bytes"
