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
module

public import Compiler.PersistedCodecTags.Core
public import Compiler.ObjectiveBendParse
public import Compiler.ObjectiveBendElaborate
public import Compiler.ObjectiveBendC4
public import Compiler.ObjectiveBendContract
public import Compiler.ObjectiveBendTermWire
public import Compiler.ObjectiveBendFrontEnd
public import Compiler.ObjectiveBendLaw
public import Compiler.Sha256
meta import Compiler.PersistedCodecTags.Core
meta import Compiler.ObjectiveBendParse
meta import Compiler.ObjectiveBendElaborate
meta import Compiler.ObjectiveBendC4
meta import Compiler.ObjectiveBendContract
meta import Compiler.ObjectiveBendTermWire
meta import Compiler.ObjectiveBendFrontEnd
meta import Compiler.ObjectiveBendLaw
meta import Compiler.Sha256

@[expose] public section

namespace Minidregg.Compiler.ObjectiveBendFrontEndIdentity
open Lean Elab Term
set_option autoImplicit false

/-- The fingerprinted sources, in manifest order (paths relative to this file's directory). -/
def sources : List String :=
  ["ObjectiveBendParse.lean", "ObjectiveBendElaborate.lean", "ObjectiveBendC4.lean",
   "ObjectiveBendTermWire.lean", "ObjectiveBendFrontEnd.lean", "Sha256.lean", "ObjectiveBendLaw.lean",
   "ObjectiveBendContract.lean"]

def manifestHeader : String := Minidregg.Compiler.PersistedCodecTags.objectivebendfrontendidentity_manifestheader_a8a75167

/-- The manifest text, read at elaboration time. -/
elab "objective_front_end_manifest%" : term => do
  let some dir := (System.FilePath.mk (← getFileName)).parent
    | throwError "front-end identity: no directory for {← getFileName}"
  -- Retain the registered header as an expression dependency. Splicing the
  -- whole manifest into one literal would erase its codec-tag provenance.
  let mut text := "\n"
  for name in sources do
    let bytes ← IO.FS.readBinFile (dir / name)
    text := text ++ name ++ " " ++ Sha256.hex bytes ++ "\n"
  return mkApp2 (mkConst ``String.append) (mkConst ``manifestHeader) (mkStrLit text)

def manifest : String := objective_front_end_manifest%

/-- The identity: the hash of the manifest (a few hundred bytes, hashed at run time). -/
def identity : String := Sha256.hexString manifest

end Minidregg.Compiler.ObjectiveBendFrontEndIdentity

/-! The TokenCensus witness of `ObjectiveBendFrontEnd.Accepted` lives here, not in its home
module: the front end's source files are fingerprinted into `identity` byte for byte, so a
theorem added to them rotates the front-end identity and every published package names a
stale one (measured: `Fixtures.NativeAcceptedFixture` refused its honest call with
`objectiveSource`). -/
namespace Minidregg.Compiler.ObjectiveBendFrontEnd
open Minidregg.Theory.ObjectiveBendTyping (decodePacket check)

/-- The checker accepted, closed, the decoded packet of this lowering, whose term is
the lowering's own erasure. -/
theorem Accepted.sound {l : Lowering} (a : Accepted l) :
    l.term.erase = .ok a.erased ∧ decodePacket l.packet = .ok a.packet ∧
      a.packet.source.term = a.erased ∧ check a.source [] a.packet.fuel = some a.typed :=
  ⟨a.erasure, a.decoded, a.packetTerm, a.checkedExact⟩

end Minidregg.Compiler.ObjectiveBendFrontEnd
