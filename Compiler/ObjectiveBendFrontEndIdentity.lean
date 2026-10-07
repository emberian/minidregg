/- The identity of the Objective Bend front end compiled into this program.

`identity` is SHA-256 (lowercase hex) of `manifest`, which lists the SHA-256 of
every source file that decides what the front end emits: the parser, the
elaborator, C4, the front-end driver and the SHA-256 used for fingerprints.
The manifest is computed while THIS module is elaborated, from the files on disk
next to it. Every listed file is imported here, so editing any of them changes its
module trace and rebuilds this one: the constant cannot go stale against the
compiled code. Anyone can recompute it with `sha256sum` (the manifest format is
one `NAME SHA256` line per file under a header line).

A source package names the front end that lowered it (`ObjectiveSourcePackage.Package.frontEnd`);
the receiver re-runs THIS front end on the package's sources and admits only a
package naming this identity (`ObjectiveBendNativeAdmission.SourceSelection`). -/
import Compiler.ObjectiveBendParse
import Compiler.ObjectiveBendElaborate
import Compiler.ObjectiveBendC4
import Compiler.ObjectiveBendTermWire
import Compiler.ObjectiveBendFrontEnd
import Compiler.ObjectiveBendLaw
import Compiler.Sha256
namespace Minidregg.Compiler.ObjectiveBendFrontEndIdentity
open Lean Elab Term
set_option autoImplicit false

/-- The fingerprinted sources, in manifest order (paths relative to this file's directory). -/
def sources : List String :=
  ["ObjectiveBendParse.lean", "ObjectiveBendElaborate.lean", "ObjectiveBendC4.lean",
   "ObjectiveBendTermWire.lean", "ObjectiveBendFrontEnd.lean", "Sha256.lean", "ObjectiveBendLaw.lean"]

def manifestHeader : String := "DREGG/OBJECTIVE-BEND/FRONT-END/v1"

/-- The manifest text, read at elaboration time. -/
elab "objective_front_end_manifest%" : term => do
  let some dir := (System.FilePath.mk (← getFileName)).parent
    | throwError "front-end identity: no directory for {← getFileName}"
  let mut text := manifestHeader ++ "\n"
  for name in sources do
    let bytes ← IO.FS.readBinFile (dir / name)
    text := text ++ name ++ " " ++ Sha256.hex bytes ++ "\n"
  return mkStrLit text

def manifest : String := objective_front_end_manifest%

/-- The identity: the hash of the manifest (a few hundred bytes, hashed at run time). -/
def identity : String := Sha256.hexString manifest

end Minidregg.Compiler.ObjectiveBendFrontEndIdentity
