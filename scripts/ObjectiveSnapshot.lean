/-
# scripts/ObjectiveSnapshot.lean -- the Objective Bend statement and axiom snapshot (Theory)

Prints the `S`/`A` rows (format: Verify/ObjectiveSnapshot.lean) of every declaration of a
module whose name starts with `Theory.ObjectiveBend`. `scripts/check-objective-proofs.sh`
compares them byte for byte with scripts/gates/objective-statements.snapshot and
scripts/gates/objective-axioms.pin; an announced change is a commit that regenerates them
(`scripts/check-objective-proofs.sh --update`): the diff of the snapshot IS the announcement.
Every other repository module of the `ObjectiveProofs` closure is pinned by
scripts/ObjectiveSnapshotMathlib.lean.

The environment is the Theory modules of the `ObjectiveProofs` target, imported one by one, not
the target itself: the rows are pretty-printed, and an imported Mathlib changes the rendering of
unchanged statements (`ℕ` for `Nat`, `∀ f ∈ fs,` for `∀ f, f ∈ fs →`, `f.2` for `f.snd`). The
target gained a Mathlib-importing Kernel module (Kernel.ObjectiveBendAdmissionSemantics, d67fd95d)
and 458 unchanged statements re-rendered. The scan refuses to run with any `Mathlib` module in
the environment, so that can never again pass for (or hide) a statement change.

The import list below (minus Verify.ObjectiveSnapshot) is read by
scripts/ObjectiveSnapshotMathlib.lean to decide what this run covers: keep it the only import
block of this file.

Run: `lake env lean scripts/ObjectiveSnapshot.lean`
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
import Verify.ObjectiveSnapshot

namespace Minidregg.ObjectiveSnapshot.TheoryRun

/-- Self-test switch (scripts/check-objective-proofs.sh flips it in a scratch copy). -/
def includeLocal : Bool := false

def config : Minidregg.ObjectiveSnapshot.Config where
  label := "objective-snapshot"
  covers := fun m => m.toString.startsWith "Theory.ObjectiveBend"
  includeLocal := includeLocal
  refuseMathlib := true
  scanFloor := 1500
  mustFind :=
    [`Minidregg.Theory.ObjectiveBendDemandMachine.stepRaw,
     `Minidregg.Theory.ObjectiveBendDemandPreservation.typed_stepRaw_preserved,
     `Minidregg.Theory.ObjectiveBendDemandAdequacy.graph_stepRaw]

end Minidregg.ObjectiveSnapshot.TheoryRun

set_option maxHeartbeats 0 in
run_meta Minidregg.ObjectiveSnapshot.main Minidregg.ObjectiveSnapshot.TheoryRun.config
