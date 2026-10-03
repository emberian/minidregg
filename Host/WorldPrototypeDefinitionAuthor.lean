import Host.Json

/-!
Pure authoring adapter over the existing public Host author and transaction
codec. This has no evaluator, authority admission or state mutation. Dummy
command coordinates only select the existing strict definition JSON parser.
-/

namespace Minidregg.Host.WorldPrototypeDefinitionAuthor

open Lean

private def sourceCommand (definition : Json) : Except String Json := do
  let descriptor ← definition.getObjVal? "descriptor"
  let target ← descriptor.getObjVal? "kind"
  return .mkObj [("subject", .str "0"), ("nonce", .str "0"),
    ("targets", .arr #[.mkObj [("kind", .str "object"), ("target", target),
      ("capability", .str "0"), ("observeCapability", .null),
      ("schemaVersion", .str "1"), ("expectedTargetRoot", .str "0"),
      ("payload", .mkObj [("type", .str "kindDefinition"), ("definition", definition)])]])]

def encode (definition : Json) : Except String (List UInt8) := do
  let authored ← Minidregg.Host.Json.author "resource" (← sourceCommand definition)
  let command ← match Kernel.DeclaredResourceController.commandCodec.decode authored with
    | some command => pure command
    | none => throw "existing resource author did not produce a canonical command"
  match command.targets with
  | [target] => match target.payload with
      | .kindDefinition definition => pure (Compiler.WorldKindCell.definitionStream.encode definition)
      | _ => throw "existing author returned another payload"
  | _ => throw "definition author requires exactly one target"

end Minidregg.Host.WorldPrototypeDefinitionAuthor

private def authoredIO {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

def main (args : List String) : IO UInt32 := do
  let [input, output] := args
    | throw (IO.userError "usage: definition-author INPUT.json OUTPUT.bin")
  if ← System.FilePath.pathExists output then
    throw (IO.userError "refusing existing definition output")
  let text ← IO.FS.readFile input
  let definition ← authoredIO (Lean.Json.parse text)
  let bytes ← authoredIO (Minidregg.Host.WorldPrototypeDefinitionAuthor.encode definition)
  IO.FS.writeBinFile output bytes.toByteArray
  return 0
