/-
Historical fn consumer progress audit. This module parses only candidate legacy
tag9 records. NativeHostReplay calls it after the original signed invocation
has been admitted, its complete record matched, and its successor validated.
No caller can turn this pure parser into a verified-history certificate.
-/
import Kernel.FnConsumerFrontierCore
import Kernel.FnConsumerProgressHistory
import Kernel.FnConsumerNamespaceAdmissionAt
import Kernel.FnConsumerNamespaceHistory

namespace Minidregg.Kernel.FnConsumerFrontierReplay

open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Kernel

set_option autoImplicit false

structure Audit where
  ordered : FnConsumerFrontierCore.State := []
  ambiguous : List FnConsumerFrontierCore.Key := []
  legacyRecords : List (FnConsumerFrontierCore.Key × FnConsumerNamespaceAdmissionAt.Legacy) := []
  registrations : List FnConsumerNamespaceHistory.Original := []
  fault : Bool := false

/-- A registration is selected by the gateway-independent namespace. Its
gateway triple and exact four-field receipt must both match the successor. -/
def Audit.registrationFor (audit : Audit) (key : FnConsumerFrontierCore.Key)
    (receipt : Receipt) : Except String FnConsumerNamespaceHistory.Original := do
  if audit.fault then throw "fn consumer frontier audit failed"
  let some original := audit.registrations.find? (fun prior =>
      prior.ingress.spec.consumerNamespace == key.namespace)
    | throw "fn consumer namespace has no admitted registration"
  unless original.matches key receipt do
    throw "fn consumer namespace registration or gateway differs"
  pure original

def Audit.registrationAbsent (audit : Audit)
    (consumerNamespace : FnConsumerFrontierCore.Namespace) : Bool :=
  !audit.registrations.any (fun prior =>
    prior.ingress.spec.consumerNamespace == consumerNamespace)

def Audit.cursor (audit : Audit) (key : FnConsumerFrontierCore.Key) :
    Except String FnConsumerFrontierCore.Cursor := do
  if audit.fault || audit.ambiguous.contains key then
    throw "fn consumer frontier is ambiguous"
  let some registration := audit.registrations.find? (fun prior =>
      prior.ingress.spec.consumerNamespace == key.namespace)
    | throw "fn consumer namespace is not registered"
  unless registration.ingress.spec.key == key do
    throw "fn consumer gateway differs from registered namespace"
  pure (FnConsumerFrontierCore.lookup audit.ordered key)

/-- Explicit adoption can select only the last unambiguous same-gateway v1
record from this walk. Other principals' copied namespace bytes neither
authorize nor poison the registered gateway. -/
def Audit.legacyFor (audit : Audit) (spec : FnConsumerNamespaceRegistration.Spec) :
    Except String (Option FnConsumerNamespaceAdmissionAt.Legacy) := do
  let key := spec.key
  if audit.fault || audit.ambiguous.contains key then
    throw "fn consumer legacy frontier is ambiguous"
  let cursor := FnConsumerFrontierCore.lookup audit.ordered key
  match spec.legacyAnchor with
  | none =>
      unless cursor.mode == .virgin && cursor.position == 0 do
        throw "fn consumer registration would reset a historical frontier"
      pure none
  | some anchor =>
      unless cursor.mode == .legacyAnchor && cursor.receipt == some anchor &&
          cursor.position == spec.initialPosition do
        throw "fn consumer registration legacy anchor differs"
      let some last := audit.legacyRecords.find? (fun entry => entry.1 == key)
        | throw "fn consumer registration legacy record is absent"
      unless last.2.receipt == anchor do
        throw "fn consumer registration legacy receipt differs"
      pure (some last.2)

/-- Called after event20 has passed native admission, full record equality,
durable advance, and successor validation. The global namespace nullifier
also prevents a second physical registration at the same namespace. -/
def Audit.register (audit : Audit) (original : FnConsumerNamespaceHistory.Original) :
    Except String Audit := do
  let consumerNamespace := original.ingress.spec.consumerNamespace
  unless audit.registrationAbsent consumerNamespace do
    throw "fn consumer namespace has duplicate registration"
  let _ ← audit.legacyFor original.ingress.spec
  pure { audit with registrations := original :: audit.registrations }

/-- Decode a possible legacy progress atom to obtain its scope, then require
`originalSkip` to verify the entire signed command, exact target and gateway
identity, nonce, marker, and retained atom. -/
def legacyTransition (domain semantics : Digest)
    (record : DurableReceiver.IntentRecord) (receipt : Receipt) :
    Option FnConsumerFrontierCore.Transition := do
  let original ← FnConsumerProgress.originalSkipAnyGatewayWithIdentity
    domain semantics record
  let exact := original.evidence
  some
    { key := ⟨exact.application, exact.scope, exact.controlBinding,
        original.subject, original.target, original.capability⟩
      kind := .legacyEmpty
      fromPosition := exact.fromPosition
      toPosition := exact.toPosition
      selectedSequence := none
      predecessor := none
      receipt := receipt }

/-- Older generic tag9 admission did not enforce a shared predecessor law.
An inconsistent chain or a same-gateway v1 write after registration poisons
future progress for that key, without retroactively invalidating the Store.
A different signed gateway cannot poison this registered namespace. -/
def Audit.adoptLegacy (audit : Audit) (record : DurableReceiver.IntentRecord)
    (transition : FnConsumerFrontierCore.Transition) : Audit :=
  if audit.ambiguous.contains transition.key then audit
  else if audit.registrations.any (fun prior =>
      prior.ingress.spec.key == transition.key) then
    { audit with ambiguous := transition.key :: audit.ambiguous }
  else
    match FnConsumerFrontierCore.step audit.ordered transition with
    | .ok ordered =>
        { audit with ordered := ordered, legacyRecords :=
            (transition.key, ⟨record, transition.receipt⟩) ::
              audit.legacyRecords.filter (fun entry => entry.1 != transition.key) }
    | .error _ => { audit with ambiguous := transition.key :: audit.ambiguous }

/-- New special transitions must extend the same verifier-minted chain. -/
def Audit.advanceV2 (audit : Audit)
    (registrationReceipt : Receipt)
    (transition : FnConsumerFrontierCore.Transition) : Except String Audit := do
  let _ ← audit.registrationFor transition.key registrationReceipt
  let _ ← audit.cursor transition.key
  let ordered ← FnConsumerFrontierCore.step audit.ordered transition
  pure { audit with ordered := ordered }

end Minidregg.Kernel.FnConsumerFrontierReplay
