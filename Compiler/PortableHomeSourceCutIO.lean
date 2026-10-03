/- Actual source-derived custody cut. Complete private image and control bytes
are captured through existing archive mechanics, not a second source journal.
This token does not establish physical process quiescence, STOP, rekey or activate.
-/
import Host.PortableContinuationInspection
import Compiler.PortableHomeTransferFrame
namespace Minidregg.Compiler.PortableHomeSourceCutIO
open Minidregg.Kernel
open Minidregg.Compiler
open Minidregg.Kernel.PortableContinuationManifest
open Minidregg.Kernel.PortableHomeTransfer
open Minidregg.Host.PortableContinuationInspection
set_option autoImplicit false

structure Captured (config : NativeHost.Config) (archive : PortableContinuationArchiveIO.NativeConfig)
    (pin : PortableHomeTransferFrame.Pin) where
  private mk ::
  audited : Audited config
  before : State
  sourceControl : Bytes
  controlExact : sourceControl = audited.source.target.snapshot.canonicalBytes pin.cell
  stateExact : PortableHomeTransferFrame.readState pin sourceControl = some before
  control : Artifact
  required : Preserves before.required audited.manifest
  controlRetained : control ∈ audited.manifest.artifacts
  readback : PortableContinuationArchiveIO.Readback archive audited.manifest

/-- Source current control selects required inventories. A caller cannot supply
an empty export list to omit pending effects, WAL/spent anchors or old-view logs.
Completeness of that CURRENT source closure still belongs to its native owners;
we do not infer it from a filesystem scan or arbitrary receipt label. -/
def capture (config : NativeHost.Config) (archive : PortableContinuationArchiveIO.NativeConfig)
    (pin : PortableHomeTransferFrame.Pin) (generation : Nat) (predecessor : Bytes)
    (artifacts : List Artifact) : IO (Except String (Captured config archive pin)) := do
  match ← NativeHostSession.startWalked config with
  | .error detail => return .error detail
  | .ok source =>
    let bytes := source.target.snapshot.canonicalBytes pin.cell
    match stateExact : PortableHomeTransferFrame.readState pin bytes with
    | none => return .error "portable current source home control missing"
    | some before =>
      try
        IO.FS.withTempDir fun directory => do
          let path := directory / "source-control.bin"
          IO.FS.writeBinFile path bytes.toByteArray
          let mode ← IO.Process.output {cmd := "/usr/bin/chmod",args := #["0600",path.toString]}
          if mode.exitCode != 0 || mode.stderr != "" then
            return .error "portable source-control private mode refused"
          let coordinate := s!"portable/current-control/cell-{pin.cell.value}".toUTF8.toList
          match ← PortableContinuationArchiveIO.captureArtifact archive coordinate path with
          | .error detail => return .error detail
          | .ok control =>
            let identity : Identity := ⟨config.deployment.domain,config.profile.semantics,config.expectedSeed⟩
            let manifest := PortableContinuationManifestCodec.fromImage identity source.target.image
              generation predecessor (control :: artifacts)
            if closed : Preserves before.required manifest then
              match ← PortableContinuationArchiveIO.retain archive manifest with
              | .error detail => return .error detail
              | .ok readback =>
                let audited := Minidregg.Host.PortableContinuationInspection.fromWalked
                  config source generation predecessor (control :: artifacts)
                return .ok ⟨audited,before,bytes,rfl,stateExact,control,closed,
                  List.mem_cons_self,readback⟩
            else return .error "portable current source inventory obligation absent"
      catch _ => return .error "portable source cut capture uncertain"

/-- Compact exact inventory references, derived only after all artifacts and
whole canonical manifest were independently reconstructed. They confer neither
participant ACK nor current-source overwrite/worker activation rights. -/
def reference {config : NativeHost.Config} {archive : PortableContinuationArchiveIO.NativeConfig}
    {pin : PortableHomeTransferFrame.Pin} (cut : Captured config archive pin) : CutReference :=
  ⟨cut.audited.manifest.prefix.identity,cut.audited.manifest.point,
    ⟨"portable/canonical-current-source-manifest-v1".toUTF8.toList,cut.readback.exactInventory⟩,
    cut.control,cut.audited.manifest.generation,cut.audited.manifest.artifacts⟩

/-- Every obligation read from actual current full control is in the cut, even
if a proposed export list omitted it. This is not a claim that privateRecovery
or service registrations are complete before their producers are installed. -/
theorem source_obligation_retained {config : NativeHost.Config}
    {archive : PortableContinuationArchiveIO.NativeConfig} {pin : PortableHomeTransferFrame.Pin}
    (cut : Captured config archive pin) (artifact : Artifact) (owed : artifact ∈ cut.before.required) :
    artifact ∈ (reference cut).required := cut.required artifact owed

#assert_axioms source_obligation_retained
end Minidregg.Compiler.PortableHomeSourceCutIO
