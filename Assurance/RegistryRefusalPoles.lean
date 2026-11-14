/-
# `Assurance/RegistryRefusalPoles.lean` — a registered effect's refusals, executed

The poles of two statements about what a requester reads when a registered effect refuses:

* `Kernel/ResourcePayloadTag.lean`, `UnboundTagNamed` (proved there): command bytes whose payload
  tag nothing reads are refused by that tag's name. Here: a command of one object target whose
  payload tag is 10 or 255 is named; the same bytes under the cited read's tag 9 or the
  observe-only read's tag 3 are not (the Host reads those), nor are bytes that stop inside the
  target's head or bytes with no frame (those are `malformedCommand`).
* `Kernel/ResourceEffectRegistry.lean`, `dispatchRefusalText`: a refusal prints its declaration's
  name, its own name, and its detail in the declaration's words. Here: a cited read's
  `citedStale` lists the fields that moved.
-/
import Kernel.ResourcePayloadTag

namespace Minidregg.Assurance.RegistryRefusalPoles
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Effects

#guard unboundTag (tagProbe [10]) == some 10
#guard unboundTag (tagProbe [255, 1, 2]) == some 255
#guard unboundTag (tagProbe [9, 0]) == none
#guard unboundTag (tagProbe [3]) == none
#guard unboundTag (tagProbe []) == none
#guard unboundTag [] == none
#guard (match decodeRefusal (tagProbe [10]) with | .effect (.unregistered 10) => true | _ => false)
#guard (match decodeRefusal (tagProbe []) with | .malformedCommand => true | _ => false)

#guard reprStr (Revival.DispatchRefusal.refused 9 "citedStale"
    (movedStream.encode [.objectField ⟨0⟩ ⟨5⟩, .programCode ⟨0⟩])) ==
  "Effect.FieldRead.citedStale [field 5, program code]"
#guard reprStr (Revival.DispatchRefusal.refused 9 "fieldNotNamed" []) == "Effect.FieldRead.fieldNotNamed"
#guard reprStr (Revival.DispatchRefusal.unregistered 10) == "Effect.Registry.unregistered 10"
#guard reprStr (Reject.effect (.refused 9 "citedStale" (movedStream.encode [.objectField ⟨0⟩ ⟨5⟩]))) ==
  "Minidregg.Kernel.DeclaredResourceController.Reject.effect (Effect.FieldRead.citedStale [field 5])"

end Minidregg.Assurance.RegistryRefusalPoles
