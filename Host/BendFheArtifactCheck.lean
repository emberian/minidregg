/- Real compiler artifact to native canonical producer conformance.
These runtime refusers exercise actual mapping; they are not a crypto proof. -/
import Host.BendFheArtifact

namespace Minidregg.Host.BendFheArtifactCheck
open Minidregg.Compiler
open Minidregg.Host.BendFheArtifact
set_option autoImplicit false

def bytes (path : String) : IO (List UInt8) := do
  let result ← IO.FS.readBinFile path
  unless result.size ≤ 4194304 do throw <| IO.userError "source file capacity"
  pure result.toList

def refuse (label : String) (artifact : BendWorldProgramCodec.Artifact)
    (compiler : List UInt8) : IO Unit := do
  match BendArtifactBinding.check artifact compiler with
  | .error _ => pure ()
  | .ok _ => match checkWireProfile artifact compiler with
    | .error _ => pure ()
    | .ok () => throw <| IO.userError ("altered native binding accepted: " ++ label)

def run (args : List String) : IO Unit := do
  let (compilerPath,checker,elaborator,kernel,implementation,base,output) ← match args with
    | [a,b,c,d,e,f,g] => pure (a,b,c,d,e,f,g)
    | _ => throw <| IO.userError
        "expected compiler checker elaborator kernel compiler-closure base native-artifact-output"
  let compiler ← bytes compilerPath
  let tools : ToolBytes := {
    checker := ← bytes checker, elaborator := ← bytes elaborator,
    kernel := ← bytes kernel, compiler := ← bytes implementation, base := ← bytes base }
  let artifact ← IO.ofExcept (produce compiler tools)
  let encoded := BendWorldProgramCodec.encode artifact
  unless BendWorldProgramCodec.decode encoded == some artifact do
    throw <| IO.userError "canonical Artifact roundtrip failed"
  refuse "source" { artifact with source :=
    { artifact.source with modules := artifact.source.modules.map
      (fun m => if m.name == "CapturedSource" then { m with bytes := m.bytes ++ [10] } else m) } } compiler
  refuse "surface-method" { artifact with source :=
    { artifact.source with entryDefinition := "missing.source.method" } } compiler
  refuse "Book" { artifact with book := artifact.book ++ [10] } compiler
  refuse "entry" { artifact with entry := "missing.entry" } compiler
  refuse "plan" { artifact with plan := digest "WRONG" [] } compiler
  refuse "carrier" { artifact with program := { artifact.program with params := [] } } compiler
  refuse "semantic-profile" { artifact with profile :=
    { artifact.profile with arithmetic := "unadmitted-arithmetic" } } compiler
  refuse "input-codec" { artifact with profile :=
    { artifact.profile with inputCodec := digest "WRONG" [] } } compiler
  refuse "output-codec" { artifact with profile :=
    { artifact.profile with outputCodec := digest "WRONG" [] } } compiler
  refuse "disclosure" { artifact with profile :=
    { artifact.profile with disclosure := digest "WRONG" [] } } compiler
  refuse "return-envelope" { artifact with profile :=
    { artifact.profile with bounds := artifact.profile.bounds.set 8 1 } } compiler
  refuse "fuel" { artifact with profile :=
    { artifact.profile with bounds := artifact.profile.bounds.set 7 0 } } compiler
  refuse "backend" { artifact with backend := "unadmitted-backend" } compiler
  refuse "changed-compiler-bytes" artifact (compiler ++ [10])
  IO.FS.writeBinFile output ⟨encoded.toArray⟩
  IO.println s!"BEND-FHE-ARTIFACT actual source/DAG binding + canonical producer/refusers PASS ({encoded.length} bytes)"

end Minidregg.Host.BendFheArtifactCheck

def main (args : List String) : IO Unit :=
  Minidregg.Host.BendFheArtifactCheck.run args
