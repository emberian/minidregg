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
* `Kernel/ReadEffects.lean`: the two root-pinning reads (codes 3 and 7) have no operand. Here:
  each one's wire bytes are its tag octet alone and decode back to it, its JSON is `type` alone
  (another field is refused), and its refusals print under its declaration's name.
* `Kernel/ResourcePayloadJson.lean`, `payloadOfJson`: which payloads a reader admits is its
  parameter. Here: the same money consent is read by the Host's reader and refused by name by the
  source agreement's, before anything of it is read (a malformed one gets the same refusal); a
  `read` and a scalar write are read by both; a type nothing bears is refused by both, naming
  what the registry binds.
-/
import Kernel.ResourcePayloadTag
import Kernel.ResourcePayloadJson

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
    ⟨(movedStream.encode [.objectField ⟨0⟩ ⟨5⟩, .programCode ⟨0⟩]).toArray⟩) ==
  "Effect.FieldRead.citedStale [field 5, program code]"
#guard reprStr (Revival.DispatchRefusal.refused 9 "fieldNotNamed" .empty) == "Effect.FieldRead.fieldNotNamed"
#guard reprStr (Revival.DispatchRefusal.unregistered 10) == "Effect.Registry.unregistered 10"
#guard reprStr (Reject.effect (.refused 9 "citedStale" ⟨(movedStream.encode [.objectField ⟨0⟩ ⟨5⟩]).toArray⟩)) ==
  "Minidregg.Kernel.DeclaredResourceController.Reject.effect (Effect.FieldRead.citedStale [field 5])"

#guard payloadStream.encode .read == [3]
#guard payloadStream.encode .kindRead == [7]
#guard (payloadStream.decodePrefix [3, 99]).map (fun d => (decide (d.1 = .read), d.2)) == some (true, [99])
#guard (payloadStream.decodePrefix [7]).map (fun d => (decide (d.1 = .kindRead), d.2)) == some (true, [])
#guard (effectNamed "read", effectNamed "kindRead") == (some 3, some 7)
#guard (match (effectAt 3).ofJson "p" (Lean.Json.mkObj [("type", "read")]) with | .ok _ => true | .error _ => false)
#guard (match (effectAt 7).ofJson "p" (Lean.Json.mkObj [("type", "kindRead"), ("root", "1")]) with
  | .ok _ => false | .error text => text == "p: unknown field root")
#guard reprStr (Revival.DispatchRefusal.refused 3 "observationRequired" .empty) == "Effect.Read.observationRequired"
#guard reprStr (Revival.DispatchRefusal.refused 7 "fieldNotNamed" .empty) == "Effect.KindRead.fieldNotNamed"

section PayloadReaders
open Minidregg.Kernel.ResourcePayloadJson

private def consent : Lean.Json :=
  Lean.Json.mkObj [("type", "moneyConsent"), ("batch", .null), ("positions", .arr #[]), ("funding", .null)]
private def scalarWrite : Lean.Json :=
  Lean.Json.mkObj [("type", "scalar"), ("actions", .arr #[])]
private def admitted (refuses : List String) (json : Lean.Json) : Bool :=
  match payloadOfJson refuses "p" json with | .ok _ => true | .error _ => false
private def refusal (refuses : List String) (json : Lean.Json) : String :=
  match payloadOfJson refuses "p" json with | .ok _ => "" | .error text => text

#guard admitted hostRefuses consent
#guard refusal agreementRefuses consent == "p.type: moneyConsent is not admitted by this reader"
#guard refusal agreementRefuses (Lean.Json.mkObj [("type", "moneyConsent")]) ==
  "p.type: moneyConsent is not admitted by this reader"
#guard admitted hostRefuses scalarWrite && admitted agreementRefuses scalarWrite
#guard admitted hostRefuses (Lean.Json.mkObj [("type", "read")]) &&
  admitted agreementRefuses (Lean.Json.mkObj [("type", "read")])
#guard refusal hostRefuses (Lean.Json.mkObj [("type", "nothing")]) ==
  refusal agreementRefuses (Lean.Json.mkObj [("type", "nothing")])
#guard (refusal hostRefuses (Lean.Json.mkObj [("type", "nothing")])).startsWith "p.type: expected append or a registered effect (scalar, content"

end PayloadReaders

end Minidregg.Assurance.RegistryRefusalPoles
