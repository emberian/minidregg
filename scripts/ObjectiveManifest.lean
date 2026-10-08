/-
# scripts/ObjectiveManifest.lean -- the Objective Bend contract manifest run (Theory)

Writes the rows and the definition closure (format: Verify/ObjectiveManifest.lean) of every
declaration of a module whose name starts with `Theory.ObjectiveBend`.
`scripts/check-objective-proofs.sh proofs` ratchets them against the per-module manifests under
scripts/gates/objective-manifest/ (scripts/objective-manifest.py): a removed row or a changed
statement, definition closure or axiom set is red unless scripts/gates/objective-contract-changes.txt
admits exactly that change. Every other repository module of the `ObjectiveProofs` closure is
covered by scripts/ObjectiveManifestMathlib.lean.

The environment is the Theory modules of the `ObjectiveProofs` target, imported one by one, not
the target itself: the rows are pretty-printed, and an imported Mathlib changes the rendering of
unchanged statements (`ℕ` for `Nat`, `∀ f ∈ fs,` for `∀ f, f ∈ fs →`, `f.2` for `f.snd`). The
target gained a Mathlib-importing Kernel module (Kernel.ObjectiveBendAdmissionSemantics, d67fd95d)
and 458 unchanged statements re-rendered. The scan refuses to run with any `Mathlib` module in
the environment, so that can never again pass for (or hide) a statement change.

The import list below (minus Verify.ObjectiveManifest) is read by
scripts/ObjectiveManifestMathlib.lean to decide what this run covers: keep it the only import
block of this file.

Run: `OBJECTIVE_MANIFEST_OUT=<file> lake env lean scripts/ObjectiveManifest.lean`
-/
import Theory.ObjectiveBendDemandInvariant
import Theory.ObjectiveBendDemandTyping
import Theory.ObjectiveBendDemandPreservation
import Theory.ObjectiveBendDemandAdequacy
import Theory.ObjectiveBendDemandCompleteness
import Theory.ObjectiveBendDemandDataSoundness
import Theory.ObjectiveBendCheckpointRoundTrip
import Theory.ObjectiveBendExtensions
import Theory.ObjectiveBendDemandCapacity
import Theory.ObjectiveBendDemandCollectProofs
import Theory.ObjectiveBendDemandSettleProofs
import Theory.ObjectiveBendDemandForceProofs
import Theory.ObjectiveBendLedgerPoles
import Theory.ObjectiveBendTemplates
import Verify.ObjectiveManifest

namespace Minidregg.ObjectiveManifest.TheoryRun

/-- Self-test switch (scripts/check-objective-proofs.sh sets it to
the prefix `Minidregg.ObjectiveManifest.Plant` in a scratch copy that plants a theorem). -/
def localPrefix : Option Lean.Name := none

def config : Minidregg.ObjectiveManifest.Config where
  label := "objective-manifest"
  covers := fun m => m.toString.startsWith "Theory.ObjectiveBend"
  localPrefix := localPrefix
  refuseMathlib := true
  scanFloor := 1500
  mustFind :=
    [`Minidregg.Theory.ObjectiveBendDemandMachine.stepRaw,
     `Minidregg.Theory.ObjectiveBendDemandPreservation.typed_stepRaw_preserved,
     `Minidregg.Theory.ObjectiveBendDemandAdequacy.graph_stepRaw]

end Minidregg.ObjectiveManifest.TheoryRun

set_option maxHeartbeats 0 in
run_meta Minidregg.ObjectiveManifest.main Minidregg.ObjectiveManifest.TheoryRun.config
