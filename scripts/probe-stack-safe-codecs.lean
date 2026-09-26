/-
Large, actual native signed-call and declared-resource command envelopes. This
exercises the receiving codecs at the byte sizes used by fn correspondence,
including exact re-encoding and failure of truncated or malformed frames.
-/
import Compiler.NativeHostCodec

open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Kernel

private def require (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"FAIL stack-safe codecs: {label}")

private def largePayload : List UInt8 := List.replicate 150000 42

private def resourceCommand : DeclaredResourceController.Command :=
  { subject := ⟨7⟩
    expectedAuthorityRoot := ⟨11⟩
    nonce := 19
    targets :=
      [{ kind := .object
         target := 600
         capability := ⟨42⟩
         schemaVersion := 1
         expectedTargetRoot := ⟨12⟩
         payload := .content ⟨[.createAtom ⟨⟨101⟩⟩ .text largePayload]⟩ }] }

private def signed : DeclaredResourceController.SignedCommand :=
  { commandBytes := DeclaredResourceController.commandCodec.encode resourceCommand
    targetEnvelopes := [List.replicate 120000 17]
    observeEnvelopes := []
    authorityEnvelope := List.replicate 110000 23 }

private def shortened (bytes : List UInt8) : List UInt8 :=
  (bytes.reverse.drop 1).reverse

def main : IO Unit := do
  let commandBytes := DeclaredResourceController.commandCodec.encode resourceCommand
  require "large declared-resource command"
    (commandBytes.length > 100000)
  match DeclaredResourceController.commandCodec.decode commandBytes with
  | some decoded =>
      require "declared-resource exact roundtrip"
        ((DeclaredResourceController.commandCodec.encode decoded).toByteArray ==
          commandBytes.toByteArray)
  | none => throw (IO.userError "FAIL stack-safe codecs: command decode")
  require "truncated declared-resource command rejected"
    ((DeclaredResourceController.commandCodec.decode (shortened commandBytes)).isNone)
  let call : SignedCall := .invoke signed
  let wire := callCodec.encode call
  require "large signed call" (wire.length > 300000)
  match callCodec.decode wire with
  | some (.invoke decoded) =>
      require "signed-call command bytes exact"
        (decoded.commandBytes.toByteArray == signed.commandBytes.toByteArray)
      require "signed-call target envelope exact"
        ((decoded.targetEnvelopes.headD []).toByteArray ==
          (signed.targetEnvelopes.headD []).toByteArray)
      require "signed-call authority envelope exact"
        (decoded.authorityEnvelope.toByteArray == signed.authorityEnvelope.toByteArray)
      require "signed-call re-encoding exact"
        ((callCodec.encode (.invoke decoded)).toByteArray == wire.toByteArray)
  | _ => throw (IO.userError "FAIL stack-safe codecs: signed-call decode")
  require "truncated signed call rejected" ((callCodec.decode (shortened wire)).isNone)
  require "malformed signed-call frame rejected" ((callCodec.decode (0 :: wire)).isNone)
  IO.println s!"PASS stack-safe declared-resource command {commandBytes.length} bytes; signed call {wire.length} bytes"
