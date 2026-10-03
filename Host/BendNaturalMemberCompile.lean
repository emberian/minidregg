/- Actual supported-member producer for Studio and native consumers.
The input names actual captured Book/surface bytes and an entry, never a graph.
Compilation refusals return structured stage diagnostics; source-native execution
of unsupported members remains a separate registered route. -/
import Compiler.BendNaturalArtifact
import Lean.Data.Json

open Lean

namespace Minidregg.Host.BendNaturalMemberCompile
open Lean (Json toJson)
open Minidregg.Compiler.BendNaturalArtifact
set_option autoImplicit false

structure Request where
  schema : String
  corePath : String
  surfacePath : String
  entry : String
  worldEntry : String
  arity : Nat
  inputOrder : List String
  fuel : Nat
  inputBits : Nat
  outputBits : Nat
  sourceBudget : Nat
  plaintextModulus : Nat
  deriving FromJson, ToJson

def compileRequest (request : Request) : IO (Except String Json) := do
  if request.schema != "dregg.bend.natural-member-input.v1" then
    return .error "unknown supported-member input schema"
  try
    let captured ← IO.FS.readFile request.corePath
    let surface ← IO.FS.readFile request.surfacePath
    if captured.utf8ByteSize > 4194304 || surface.utf8ByteSize > 4194304 then
      return .error "source byte capacity exceeded"
    return produce request.arity captured surface request.entry request.worldEntry
      request.inputOrder request.fuel request.inputBits request.outputBits
      request.sourceBudget request.plaintextModulus
  catch error => return .error ("source read: " ++ error.toString)

def diagnostic (message : String) : Json :=
  Json.mkObj [("schema",toJson "dregg.bend.compiler-diagnostic.v1"),
    ("stage",toJson "supported-natural-member"),("message",toJson message)]

end Minidregg.Host.BendNaturalMemberCompile

def main (args : List String) : IO UInt32 := do
  let [requestPath, outputPath] := args | do
    IO.eprintln "usage: bend-natural-member REQUEST_JSON OUTPUT_JSON"
    return (2 : UInt32)
  try
    let raw ← IO.FS.readFile requestPath
    let request : Except String Minidregg.Host.BendNaturalMemberCompile.Request := do
      fromJson? (← Json.parse raw)
    let result ← match request with
      | .error reason => pure (.error reason)
      | .ok spec => Minidregg.Host.BendNaturalMemberCompile.compileRequest spec
    match result with
    | .error reason =>
      IO.FS.writeFile outputPath ((Minidregg.Host.BendNaturalMemberCompile.diagnostic reason).compress ++ "\n")
      return (2 : UInt32)
    | .ok artifact =>
      IO.FS.writeFile outputPath (artifact.compress ++ "\n")
      return (0 : UInt32)
  catch error => IO.eprintln error.toString; return (2 : UInt32)
