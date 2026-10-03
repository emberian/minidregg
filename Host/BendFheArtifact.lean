/- Canonical source-bearing BFV artifact production. The compiler mapping is
checked, while these opaque wire-return codecs grant no native computation,
encrypted-input domain, security estimate, custody or release authority. -/
import Compiler.BendArtifactBinding

namespace Minidregg.Host.BendFheArtifact
open Lean
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

/-- Exact deployment-selected implementation bytes, not claimed upstream hashes.
Compiler is an ordered framed closure supplied by the deployment producer. -/
structure ToolBytes where
  checker : List UInt8
  elaborator : List UInt8
  kernel : List UInt8
  compiler : List UInt8
  base : List UInt8

def digest (role : String) (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash ("DREGG.BEND.FHE/" ++ role ++ "/v1").toUTF8.toList bytes).digest

def components (tools : ToolBytes) : List Digest :=
  [digest "CHECKER" tools.checker, digest "ELABORATOR" tools.elaborator,
   digest "KERNEL" tools.kernel, digest "COMPILER" tools.compiler,
   digest "BASE" tools.base]

def physicalProfile (json : Json) : Except String String := do
  let schema ← BendArtifactBinding.string json "schema"
  if schema == "dregg.bend.prelude-bool-case.v1" then
    pure "bfv-fhe011-degree4096-t1032193-public-prelude-bool-case-depth0-v1"
  else if schema == "dregg.bend.prelude-bool-mux.v1" then
    pure "bfv-fhe011-degree4096-t1032193-public-prelude-bool-mux-plan-depth1-lifetime2-v1"
  else if schema == "dregg.bend.public-natural-expression.v1" then
    pure "bfv-fhe011-degree4096-t1032193-public-natural-add-fresh-depth0-v1"
  else throw "source-bearing BFV compiler schema required"

def inputCodec (physical : String) (compilerBytes : List UInt8) : Digest :=
  digest "INPUT-SCALAR-4096"
    ("dregg.fhe-bend.request.v1;scalar-simd;slots=4096;".toUTF8.toList ++
      physical.toUTF8.toList ++ compilerBytes)
def outputCodec : Digest := digest "OPAQUE-COMPLETION"
  "dregg.fhe-bend.completion-candidate.v1;slots=4096;bytes=524288".toUTF8.toList
def effectAbi : Digest := digest "EFFECTS" "opaque-custody-empty-effects-v1".toUTF8.toList
def disclosure : Digest := digest "DISCLOSURE"
  "public-program;honest-owner-input;private-output;current-authority-release-v1".toUTF8.toList

/-- Physical representation choice is derived from exact source compiler bytes.
This gate is additional to compiler source/DAG equivalence. -/
def checkWireProfile (artifact : BendWorldProgramCodec.Artifact)
    (compilerBytes : List UInt8) : Except String Unit := do
  let some raw := String.fromUTF8? ⟨compilerBytes.toArray⟩ | throw "compiler UTF-8 refused"
  let json ← Json.parse raw
  let physical ← physicalProfile json
  let selectedDefinition ← if (← BendArtifactBinding.string json "schema") ==
      "dregg.bend.public-natural-expression.v1" then
    BendArtifactBinding.string json "arithmeticEntry"
    else BendArtifactBinding.string json "entry"
  unless artifact.source.entryDefinition == selectedDefinition &&
      artifact.profile.inputCodec == inputCodec physical compilerBytes &&
      artifact.profile.outputCodec == outputCodec &&
      artifact.profile.effectAbi == effectAbi &&
      artifact.profile.disclosure == disclosure &&
      artifact.profile.bounds[8]? == some 524288 do
    throw "opaque physical input/output/effect/disclosure profile differs"

/-- The artifact is an immutable opaque-result carrier. Empty native ABI slots
do not claim it executes the compiler's affine byte-list wrapper. -/
def produce (compilerBytes : List UInt8) (tools : ToolBytes) :
    Except String BendWorldProgramCodec.Artifact := do
  unless [tools.checker,tools.elaborator,tools.kernel,tools.compiler,tools.base].all
      (fun bytes => !bytes.isEmpty) do throw "exact tool/base source bytes required"
  let some raw := String.fromUTF8? ⟨compilerBytes.toArray⟩
    | throw "compiler UTF-8 refused"
  let json ← Json.parse raw
  let physical ← physicalProfile json
  let surface ← BendArtifactBinding.string json "surfaceSource"
  let entry ← BendArtifactBinding.string json "entry"
  let selectedDefinition ← if (← BendArtifactBinding.string json "schema") ==
      "dregg.bend.public-natural-expression.v1" then
    BendArtifactBinding.string json "arithmeticEntry"
    else pure entry
  let core ← BendCoreAdmission.canonicalize
    (← BendArtifactBinding.string json "bookSource").toUTF8.toList
  let budget ← if (← BendArtifactBinding.string json "schema") ==
      "dregg.bend.public-natural-expression.v1" then
    BendArtifactBinding.natural json "sourceBudget"
    else pure 1
  let package : BendWorldSource.Package := {
    modules := [
      ⟨"Base", tools.base, []⟩,
      ⟨"CapturedSource", surface.toUTF8.toList,
        [⟨"", 0, BendWorldSource.sourceId tools.base⟩]⟩]
    entryModule := 1
    entryDefinition := selectedDefinition }
  let profile : BendWorldProgramCodec.Profile := {
    upstream := BendWorldSource.upstreamPin
    components := components tools
    evaluator := Minidregg.Kernel.BendNativeRun.evaluatorId
    semantics := "bendtt-eval-walk-947db722-v1"
    arithmetic := "bendtt-structural-nat-exact-v1"
    charge := Minidregg.Kernel.BendNativeRun.chargeId
    inputCodec := inputCodec physical compilerBytes
    outputCodec := outputCodec
    effectAbi := effectAbi
    disclosure := disclosure
    bounds := [tools.base.length + surface.toUTF8.size + 1, core.bytes.length + 1,
      128,1024,4096,4096,4096,budget,524288] }
  let artifact : BendWorldProgramCodec.Artifact := {
    source := package, profile := profile, book := core.bytes, entry := entry
    plan := BendArtifactBinding.planId compilerBytes
    backend := "bfv-public-source-v1"
    program := {
      evaluator := profile.evaluator, jam := core.bytes
      abi := {
        version := NockProgramCodec.abiVersion
        sample := []
        outputs := []
        libraries := []
        fuel := 1
        door := none
        context := .pinned }
      params := BendArtifactBinding.entryParams entry } }
  let _ ← BendArtifactBinding.check artifact compilerBytes
  checkWireProfile artifact compilerBytes
  pure artifact

end Minidregg.Host.BendFheArtifact
