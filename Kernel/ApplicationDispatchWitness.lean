/-
The expected app state for a future checked dispatch receiver. The app is
observed under a current signed read grant and added as a durable read guard;
its lifecycle page is not mutated by a participant's request. This candidate
comparison is not delivery authority. The durable special event/nullifier
retains the complete pending request, without a bounded content atom.
-/
import Kernel.ApplicationGrain
import Kernel.ApplicationDispatchIngress

namespace Minidregg.Kernel.ApplicationDispatchWitness

open Minidregg.Compiler
open Minidregg.Kernel.ApplicationDispatchCodec

set_option autoImplicit false

/-- The app phase is fixed at serving. The future native observation receiver
must parse all four coordinates from its actual loaded app page, then compare
to this value and guard that exact root in the same durable intent. -/
def servingState (dispatch : Dispatch) : ApplicationGrain.State where
  generation := dispatch.app.generation
  phase := 4
  packageVersion := dispatch.app.packageVersion
  snapshotVersion := dispatch.app.snapshotVersion

def matchesServing (dispatch : Dispatch) (actual : ApplicationGrain.State) : Bool :=
  decide (actual = servingState dispatch)

theorem matchesServing_exact (dispatch : Dispatch) (actual : ApplicationGrain.State)
    (accepted : matchesServing dispatch actual = true) :
    actual = servingState dispatch := by
  simpa [matchesServing] using accepted

end Minidregg.Kernel.ApplicationDispatchWitness
