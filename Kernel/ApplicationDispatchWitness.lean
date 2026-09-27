/-
Exact source-derived app and pending-journal incidences for a future checked
dispatch receiver. These constructors do not authorize delivery: the real
receiver must also admit the current session/parent and installed manifest
under one signed command and create the distinct special dispatch event.
-/
import Kernel.ApplicationGrain
import Kernel.ApplicationDispatchIngress

namespace Minidregg.Kernel.ApplicationDispatchWitness

open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument
open Minidregg.Kernel.ApplicationDispatchCodec
open Minidregg.Kernel.ApplicationDispatchIngress

set_option autoImplicit false

/-- The app phase is fixed at serving. Each of its four old coordinates is
checked by `ApplicationGrain.Operation.servingWitness` and by DRC against the
actual loaded page. A caller cannot substitute a newer generation or package. -/
def servingState (dispatch : Dispatch) : ApplicationGrain.State where
  generation := dispatch.app.generation
  phase := 4
  packageVersion := dispatch.app.packageVersion
  snapshotVersion := dispatch.app.snapshotVersion

def appTarget (dispatch : Dispatch) (expectedRoot : Digest) :
    DeclaredResourceController.Target :=
  ApplicationGrain.Operation.target .servingWitness
    dispatch.app.resource dispatch.app.capability expectedRoot
    (servingState dispatch)

theorem app_target_state_exact (dispatch : Dispatch) (expectedRoot : Digest) :
    (appTarget dispatch expectedRoot).payload =
      .scalar (ApplicationGrain.actions dispatch.app.resource
        (servingState dispatch) (servingState dispatch)) := rfl

/-- The pending atom contains the complete canonical request, including
ordered headers and body, not a claimed digest or a noop context marker.
The atom is not trusted as a permit without a native special admission. -/
def pendingAtom (ingress : Ingress) : AtomId :=
  ⟨⟨(keyDigest ingress).value⟩⟩

def journalTarget (ingress : Ingress) (journalResource : Nat)
    (capability : CapabilityId) (expectedRoot : Digest) :
    DeclaredResourceController.Target :=
  { kind := .object
    target := journalResource
    capability := capability
    schemaVersion := ContentResource.commandVersion
    expectedTargetRoot := expectedRoot
    payload := .content ⟨[.createAtom (pendingAtom ingress)
      (.inlineObject ⟨12⟩) ingress.dispatch.canonicalBytes]⟩ }

theorem journal_target_exact (ingress : Ingress) (journalResource : Nat)
    (capability : CapabilityId) (expectedRoot : Digest) :
    (journalTarget ingress journalResource capability expectedRoot).payload =
      .content ⟨[.createAtom (pendingAtom ingress)
        (.inlineObject ⟨12⟩) ingress.dispatch.canonicalBytes]⟩ := rfl

end Minidregg.Kernel.ApplicationDispatchWitness
