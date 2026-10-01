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
  | _, .tickClock => "tickClock"

/-- Every authorable head field comes from the decoded source capability.
Canonical bytes retain the full ancestry, which is not recreated in JSON. -/
def headJson {kind : ResourceKind} (cap : Capability kind) : Json := .mkObj
  [("id", decimal cap.id.value), ("root", decimal cap.root.value),
   ("parent", cap.parent.map (fun p => decimal p.value) |>.getD .null),
   ("issuer", decimal cap.issuer.value),
   ("holder", match cap.holder with
     | .bearer => .mkObj [("type", "bearer")]
     | .subject s => .mkObj [("type", "subject"), ("subject", decimal s.value)]),
   ("targets", numbers (cap.scope.targets.image (·.value))),
   ("verbs", .arr <| ((cap.scope.verbs.image verbTag).sort (· ≤ ·)).toArray.map
     (fun tag => verbName (verbOfTag kind tag))),
   ("maxCost", decimal cap.scope.maxCost),
   ("notBefore", decimal cap.notBefore), ("notAfter", decimal cap.notAfter),
   ("issuerEpoch", decimal cap.issuerEpoch), ("policyId", decimal cap.policyId.value),
   ("policyEpoch", decimal cap.policyEpoch),
   ("ancestors", numbers (cap.ancestors.image (·.value))),
   ("channels", numbers (cap.channels.image (·.value)))]

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
