/- Source-owned presentation of a stored capability returned by an authorized
query. The resource kind is supplied by that signed query, not inferred from
the bytes. This structural view does not establish current authority. -/
import Compiler.CredentialAuthorityEntryCodec
import Lean.Data.Json

namespace Minidregg.Host.CapabilityInspection

open Lean
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.CredentialAuthorityEntryCodec

set_option autoImplicit false

private def decimal (n : Nat) : Json := .str (toString n)

private def hex (bytes : List UInt8) : Json := .str <| String.ofList <|
  bytes.flatMap fun byte =>
    let digits := "0123456789abcdef".toList
    [digits[byte.toNat / 16]?.getD '0', digits[byte.toNat % 16]?.getD '0']

private def numbers (values : Finset Nat) : Json :=
  .arr <| (values.sort (· ≤ ·)).toArray.map decimal

private def verbName : {kind : ResourceKind} → Verb kind → Json
  | _, .observeObject | _, .observeAccount | _, .observeProgram => "observe"
  | _, .mutateObject => "mutate"
  | _, .transfer => "transfer"
  | _, .installProgram => "install"
  | _, .delegateObject | _, .delegateAccount | _, .delegateProgram => "delegate"
  | _, .installPolicy => "installPolicy"
  | _, .revokeCapability => "revokeCapability"
  | _, .appendObject => "append"
  | _, .mintAsset => "mintAsset"
  | _, .burnAsset => "burnAsset"
  | _, .observePayment => "observePayment"
  | _, .tickClock => "tickClock"
  | _, .placeObject => "place"
  | _, .reserveObject | _, .reserveAccount | _, .reserveProgram => "reserve"

/-- K-FIELDS: `fields` (sorted names) only when the scope names some, and
`maxDelta` only when it sets a bound; absent keys are every field / no bound. -/
def fieldsJson {kind : ResourceKind} (scope : Scope kind) : List (String × Json) :=
  (match scope.fields with
    | none => []
    | some named => [("fields", .arr <| ((named.image fieldLabel).sort (· ≤ ·)).toArray.map
        fun label => .str (cellFieldName (fieldOfLabel label)))]) ++
  (if scope.maxDelta = ∅ then [] else
    [("maxDelta", .arr <| ((scope.maxDelta.image boundLabel).sort (· ≤ ·)).toArray.map
      fun label =>
        let bound := boundOfLabel label
        .mkObj [("field", .str (cellFieldName bound.1)), ("max", decimal bound.2)])])

/-- Every authorable head field comes from the decoded source capability.
Canonical bytes retain the full ancestry, which is not recreated in JSON. -/
def headJson {kind : ResourceKind} (cap : Capability kind) : Json := .mkObj
  ([("id", decimal cap.id.value), ("root", decimal cap.root.value),
   ("parent", cap.parent.map (fun p => decimal p.value) |>.getD .null),
   ("issuer", decimal cap.issuer.value),
   ("holder", match cap.holder with
     | .bearer => .mkObj [("type", "bearer")]
     | .subject s => .mkObj [("type", "subject"), ("subject", decimal s.value)]),
   (match cap.scope.targets with
     | .explicit targets => ("targets", numbers (targets.image (·.value)))
     | .under room => ("room", decimal room)),
   ("verbs", .arr <| ((cap.scope.verbs.image verbTag).sort (· ≤ ·)).toArray.map
     (fun tag => verbName (verbOfTag kind tag))),
   ("maxCost", decimal cap.scope.maxCost),
   ("notBefore", decimal cap.notBefore), ("notAfter", decimal cap.notAfter),
   ("issuerEpoch", decimal cap.issuerEpoch), ("policyId", decimal cap.policyId.value),
   ("policyEpoch", decimal cap.policyEpoch),
   ("ancestors", numbers (cap.ancestors.image (·.value))),
   ("channels", numbers (cap.channels.image (·.value)))] ++ fieldsJson cap.scope)

def inspect (kind : ResourceKind) (bytes : List UInt8) : Except String Json := do
  let codec := (storedCapabilityStream kind).toLawful
  let some stored := codec.decode bytes
    | throw "noncanonical stored capability"
  unless codec.encode stored == bytes do
    throw "stored capability encoding alias"
  pure <| .mkObj [("type", "capability"),
    ("kind", match kind with | .object => "object" | .account => "account" | .program => "program"),
    ("canonical", hex bytes), ("head", headJson stored.head),
    ("ancestryCount", decimal stored.ancestry.length)]

end Minidregg.Host.CapabilityInspection
