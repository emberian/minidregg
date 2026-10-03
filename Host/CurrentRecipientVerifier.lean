/- Closed pinned-local verifier entrypoint, invoked under existing client
custody lock/manifest. This is not a public key query or remote proof decoder.
Source release authorization/publication remain separate guarded operations. -/
import Kernel.NativeCurrentMemberKeyIO
import Lean
namespace Minidregg.Host.CurrentRecipientVerifier
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.NativeCurrentMemberKeyIO
set_option autoImplicit false

/-- ABI: CONFIG inspect current-recipient INPUT.bin OUTPUT.bin.
CONFIG is opened by the host's existing pinned Settings reader. INPUT is exact
DREGG.CURRENT.RECIPIENT.QUERY/v1; OUTPUT is exact native-local readback claim.
The client must pin verifier/config and verify complete input/domain/semantics/
continuity point under its existing custody lock. Remote stdout is insufficient.
A fresh empty output file/path is mandatory so failed verification cannot retain old success. -/
def run (config : Config) (input output : System.FilePath) : IO UInt32 := do
  try
    if ← output.pathExists then
      let old ← IO.FS.withFile output .read (fun handle => handle.read 1)
      if old.size != 0 then return (1 : UInt32)
    let bytes ← IO.FS.withFile input .read (fun handle => handle.read 4097)
    if bytes.size > 4096 then return (1 : UInt32)
    let some request := decode bytes.toList | return (1 : UInt32)
    match ← authenticate config request with
    | .error _ => return (1 : UInt32)
    | .ok readback =>
      let response := readback.response.toByteArray
      if response.size > 8192 then return (1 : UInt32)
      IO.FS.writeBinFile output response
      IO.setAccessRights output {user := {read := true,write := true}}
      return (0 : UInt32)
  catch _ => return (1 : UInt32)

private def hexDigits : Array Char := "0123456789abcdef".toList.toArray
def hex (bytes : List UInt8) : String :=
  String.ofList (bytes.flatMap (fun b => [hexDigits[b.toNat / 16]!,hexDigits[b.toNat % 16]!]))
private def unhexList : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
      let hi ← "0123456789abcdef".toList.findIdx? (· == a)
      let lo ← "0123456789abcdef".toList.findIdx? (· == b)
      return UInt8.ofNat (hi * 16 + lo) :: (← unhexList rest)
  | _ => none
def unhex (s : String) : Option (List UInt8) := do
  let bytes ← unhexList s.toList
  if hex bytes = s then some bytes else none

structure AuthorInput where
  pointHeight : Nat
  /-- Canonical decimal string preserves the full unsigned source-root Nat. -/
  pointRoot : String
  member : Nat
  room : Nat
  keysCell : Nat
  payloadHex : String
  deriving Lean.FromJson, Lean.ToJson

private def freshOutput (path : System.FilePath) : IO Bool := do
  if ← path.pathExists then
    let bytes ← IO.FS.withFile path .read (fun h => h.read 1)
    return bytes.size == 0
  return true

/-- author current-recipient-query JSON -> QUERY. This creates a claim only;
point must originate in the client's existing locked continuity anchor. -/
def author (input output : System.FilePath) : IO UInt32 := do
  try
    if !(← freshOutput output) then return (1 : UInt32)
    let bytes ← IO.FS.withFile input .read (fun h => h.read 8193)
    if bytes.size > 8192 then return (1 : UInt32)
    let some text := String.fromUTF8? bytes | return (1 : UInt32)
    let .ok json := Lean.Json.parse text | return (1 : UInt32)
    let .ok fields := Lean.fromJson? (α := AuthorInput) json | return (1 : UInt32)
    let some root := fields.pointRoot.toNat? | return (1 : UInt32)
    if toString root != fields.pointRoot then return (1 : UInt32)
    let some payload := unhex fields.payloadHex | return (1 : UInt32)
    let some claim := Minidregg.Compiler.CurrentRecipientRecord.decode ⟨fields.member⟩ payload | return (1 : UInt32)
    if claim.room != fields.room || claim.keysCell != fields.keysCell then return (1 : UInt32)
    let request : Request := ⟨⟨fields.pointHeight,⟨root⟩⟩,⟨fields.member⟩,fields.room,fields.keysCell,payload⟩
    let wire := requestBytes request
    if wire.length > 4096 then return (1 : UInt32)
    IO.FS.writeBinFile output wire.toByteArray
    IO.setAccessRights output {user := {read := true,write := true}}
    return (0 : UInt32)
  catch _ => return (1 : UInt32)

/-- Pure parser for a native-local CLAIM. Invoking it on an operator's arbitrary
bytes does not authenticate a recipient. The client consumes this ONLY after
its pinned local actual-source inspect operation succeeded under custody lock. -/
def inspectReadback (config : Config) (input output : System.FilePath) : IO UInt32 := do
  try
    if !(← freshOutput output) then return (1 : UInt32)
    let bytes ← IO.FS.withFile input .read (fun h => h.read 8193)
    if bytes.size > 8192 then return (1 : UInt32)
    let frame := "DREGG.CURRENT.RECIPIENT.READBACK".toUTF8.toList ++ [1]
    if bytes.toList.take frame.length != frame then return (1 : UInt32)
    let stream := Minidregg.Compiler.Tower256ConcreteBackend.StreamCodec.product Minidregg.Compiler.Tower256ConcreteBackend.bytesStream
      (Minidregg.Compiler.Tower256ConcreteBackend.StreamCodec.product Minidregg.Compiler.Tower256ConcreteBackend.digestStream
      (Minidregg.Compiler.Tower256ConcreteBackend.StreamCodec.product Minidregg.Compiler.Tower256ConcreteBackend.digestStream
      (Minidregg.Compiler.Tower256ConcreteBackend.StreamCodec.product Minidregg.Compiler.Tower256ConcreteBackend.StreamCodec.nat
      (Minidregg.Compiler.Tower256ConcreteBackend.StreamCodec.product Minidregg.Compiler.Tower256ConcreteBackend.StreamCodec.nat
        Minidregg.Compiler.Tower256ConcreteBackend.bytesStream))))
    let body := bytes.toList.drop frame.length
    let some decoded := stream.toLawful.decode body | return (1 : UInt32)
    if stream.encode decoded != body then return (1 : UInt32)
    let (query,domain,semantics,keyID,keyEpoch,publicKey) := decoded
    let some request := decode query | return (1 : UInt32)
    let some claim := Minidregg.Compiler.CurrentRecipientRecord.decode request.member request.payload | return (1 : UInt32)
    if domain != config.deployment.domain || semantics != config.profile.semantics ||
        claim.room != request.room || claim.keysCell != request.keysCell ||
        publicKey != claim.signingKey || keyEpoch != claim.epoch then return (1 : UInt32)
    let json := Lean.Json.mkObj [
      ("queryHex",Lean.toJson (hex query)),("domain",Lean.toJson (toString domain.value)),
      ("semantics",Lean.toJson (toString semantics.value)),("keyID",Lean.toJson (toString keyID)),
      ("keyEpoch",Lean.toJson keyEpoch),("publicKeyHex",Lean.toJson (hex publicKey)),
      ("pointHeight",Lean.toJson request.point.height),("pointRoot",Lean.toJson (toString request.point.root.value)),
      ("member",Lean.toJson request.member.value),("room",Lean.toJson request.room),("keysCell",Lean.toJson request.keysCell)]
    IO.FS.writeFile output (json.compress ++ "\n")
    IO.setAccessRights output {user := {read := true,write := true}}
    return (0 : UInt32)
  catch _ => return (1 : UInt32)
end Minidregg.Host.CurrentRecipientVerifier
