/- Reference closure loading consumes current authorized content reads at
EXACT pinned roots. Changed/retired/unreadable atoms refuse. No mutable latest
lookup, unobserved host package or detached success flag supplies source. -/
import Kernel.ObjectiveBendReferenceSource
import Kernel.ObjectiveBendInstanceLoader
import Compiler.ObjectiveBendReferenceInstance
namespace Minidregg.Kernel.ObjectiveBendReferenceLoader
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.BendTT
open ObjectiveBendReference
set_option autoImplicit false
variable {F : Type} [Field F] [DecidableEq F]
  {deployment : ResourceObservationAdmission.Deployment}
  {durable : ResourceObservationAdmission.Durable}
  {context : ResourceObservationAdmission.Context deployment durable}
  {profile : CanonicalRuntimeProfile.Profile F} {subject : TypedAuthorization.SubjectId}

def find (reference : Reference)
    (observations : List (BendInvocationInput.Admitted context profile subject)) :
    Option (BendInvocationInput.Admitted context profile subject) :=
  observations.find? fun observation => decide
    (observation.value.resource = reference.resource ∧ observation.value.root = reference.root)

/-- Each resolved partial retains its actual admitted source token. A finite
source observation can serve several atoms in the same exact immutable image. -/
def loadPartials (pin : Pin)
    (observations : List (BendInvocationInput.Admitted context profile subject)) :
    Except String (List ObjectiveBendPrototype.Partial) :=
  pin.partials.mapM fun reference => do
    let some current := find reference observations | throw "missing current pinned source observation"
    let some loaded := ObjectiveBendReferenceSource.loadPartial reference current
      | throw "unreadable, changed or retired partial source"
    pure loaded.prototype

structure LoadedStore (store : Minidregg.Theory.Store.Store WorldKindCell.instanceLayout) where
  private mk ::
  object : ObjectiveBendReferenceInstance.Instance
  native : WorldKindCell.instanceAt store = some object.value
  observations : List (BendInvocationInput.Admitted context profile subject)

/-- Reconstruct exact generated methods from actual reflected partials. The
helper Book is the pinned checked core with ONLY those exact generated names
removed; the constructive linker must reproduce its complete canonical bytes. -/
def load (store : Minidregg.Theory.Store.Store WorldKindCell.instanceLayout)
    (observations : List (BendInvocationInput.Admitted context profile subject)) :
    Except String (LoadedStore (context := context) (profile := profile) (subject := subject) store) := do
  match native : WorldKindCell.instanceAt store with
  | none => throw "invalid native world object"
  | some value =>
    let some space := ObjectiveBendInstanceLoader.pinSpace value.descriptor
      | throw "missing unique semantic ROM prototype pin"
    match pinned : ObjectiveBendReferenceInstance.pinAt value space with
    | none => throw "invalid canonical compact prototype reference pin"
    | some pin =>
      let partials ← loadPartials pin observations
      let some current := find pin.core observations | throw "missing current pinned core observation"
      let some core := ObjectiveBendReferenceSource.loadCore pin.core current
        | throw "unreadable, changed or retired core source"
      let specs ← partials.mapM ObjectiveBendPrototype.reflect
      let checked ← BendCoreAdmission.admit core.core.book
      let names := (ObjectiveBendLinker.generated specs).map Def.k
      let helpers := checked.book.filter fun definition => !names.contains definition.k
      let closure : ObjectiveBendInstance.Pin := ⟨partials, core.core.book⟩
      let source ← ObjectiveBendInstanceLoader.loadPin helpers closure
      if identities : Matches pin partials core.core then
        pure ⟨⟨value, space, pin, pinned, closure, source, core.core, rfl, identities⟩,
          native, observations⟩
      else throw "loaded closure differs from persistent reference identities"
end Minidregg.Kernel.ObjectiveBendReferenceLoader
