/- Native artifact custody uses SHA-256 over exact retained file bytes.
This is a code/configuration pin, not a semantic authority assertion. -/
import Lean

namespace Minidregg.Compiler.RetainedArtifactIO

set_option autoImplicit false

def canonicalSha256 (text : String) : Bool :=
  text.length == 64 && text.toList.all fun character =>
    decide (('0' ≤ character ∧ character ≤ '9') ∨ ('a' ≤ character ∧ character ≤ 'f'))

def fileSha256 (path : System.FilePath) : IO (Except String String) := do
  try
    let output ← IO.Process.output { cmd := "/usr/bin/sha256sum", args := #[path.toString] }
    if output.exitCode != 0 || output.stderr != "" then return .error "retained artifact hash failed"
    let text := (output.stdout.splitOn " ").head!
    if canonicalSha256 text then return .ok text
    else return .error "retained artifact hash response malformed"
  catch error => return .error s!"retained artifact unavailable: {error}"

def checkedFile (path : System.FilePath) (expected : String) : IO (Except String Unit) := do
  if !canonicalSha256 expected then return .error "retained artifact pin malformed"
  match ← fileSha256 path with
  | .error detail => return .error detail
  | .ok actual =>
      if actual == expected then return .ok ()
      else return .error "retained artifact differs from trusted pin"

end Minidregg.Compiler.RetainedArtifactIO
