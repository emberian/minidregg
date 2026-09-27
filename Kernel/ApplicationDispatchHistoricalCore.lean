/-
Cycle-safe source evidence for app share issuance and current dispatch.
An `IssuedEvidence` proves one issue was natively admitted and its COMPLETE
intent equals an exact record. It does not prove that this record belongs to
the current admitted history. NativeHostReplay must mint that chronological
membership during its replay walk before a dispatch event can be admitted;
the upper live receiver uses the verifier-selected original prefix.
-/
import Kernel.ApplicationDispatchPending
import Kernel.ApplicationShareIssueReceiver
import Kernel.NativeHostContext

namespace Minidregg.Kernel.ApplicationDispatchHistoricalCore

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceBirth
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.ApplicationDispatchAdmission
open Minidregg.Kernel.ApplicationShareIssueSource

set_option autoImplicit false

/-- Source admission and full intent equality, with the large original
physical image and admitted object retained only in proof-erased Prop. The
record is not yet certified as belonging to the current history. -/
structure IssuedEvidence (config : Config) where
  private mk ::
  ingress : ApplicationShareIssueSource.Ingress
  descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry
  record : DurableReceiver.IntentRecord
  sourceExact :
    ∃ (pins : FactoryPins)
      (original : ResourceBirthController.Concrete.Durable)
      (height : Height)
      (accepted : ApplicationShareIssueAdmission.Accepted config.profile config
        pins original height ingress),
      descriptor = accepted.birth.descriptor ∧
        record = DurableReceiver.IntentRecord.ofIntent
          (ApplicationShareIssueReceiver.intent accepted)

/-- A bare ticket or event cannot call this factory: it needs the actual
private native Accepted issue and exact equality of all recorded intent
fields. The caller must separately prove chronological membership in an
admitted replay prefix before using this evidence for a dispatch. -/
def IssuedEvidence.fromAccepted (config : Config) (pins : FactoryPins)
    (original : ResourceBirthController.Concrete.Durable) (height : Height)
    (ingress : ApplicationShareIssueSource.Ingress)
    (accepted : ApplicationShareIssueAdmission.Accepted config.profile config
      pins original height ingress)
    (record : DurableReceiver.IntentRecord)
    (exact : record = DurableReceiver.IntentRecord.ofIntent
      (ApplicationShareIssueReceiver.intent accepted)) : IssuedEvidence config :=
  ⟨ingress, accepted.birth.descriptor, record,
    ⟨pins, original, height, accepted, rfl, exact⟩⟩

def IssuedEvidence.transactionId {config : Config} (issued : IssuedEvidence config) : Digest :=
  issued.descriptor.transactionId

def IssuedEvidence.eventId {config : Config} (issued : IssuedEvidence config) : Digest :=
  (ApplicationShareIssueReceiver.event config.deployment.domain issued.ingress).eventId

theorem IssuedEvidence.record_transaction {config : Config} (issued : IssuedEvidence config) :
    issued.record.transactionId = issued.transactionId := by
  rcases issued.sourceExact with ⟨_, _, _, accepted, descriptorExact, recordExact⟩
  rw [recordExact]
  change (ApplicationShareIssueReceiver.intent accepted).transactionId =
    issued.descriptor.transactionId
  rw [descriptorExact]
  rfl

theorem IssuedEvidence.record_event {config : Config} (issued : IssuedEvidence config) :
    issued.record.event =
      ApplicationShareIssueReceiver.event config.deployment.domain issued.ingress := by
  rcases issued.sourceExact with ⟨_, _, _, accepted, _, recordExact⟩
  rw [recordExact]
  rfl

/-- Core selection is only a *current-image component*. The issue evidence
must be added to a verifier-minted chronological context before this candidate
can be committed or handed to a physical app. -/
structure CheckedCandidate (config : Config) (durable : NativeHost.Durable)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (issued : IssuedEvidence config) where
  private mk ::
  issueBytesExact : ingress.issueIngressBytes =
    ApplicationShareIssueSource.ingressCodec.encode issued.ingress
  checked : ApplicationDispatchAdmission.CheckedCurrent config.deployment config.profile
    ⟨config.federation, NativeHost.logicalHeight config durable⟩ durable ingress
    issued.ingress.spec issued.descriptor

def checkCurrent (config : Config) (durable : NativeHost.Durable)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (issued : IssuedEvidence config) :
    IO (Except String (CheckedCandidate config durable ingress issued)) := do
  if issueBytesExact : ingress.issueIngressBytes =
      ApplicationShareIssueSource.ingressCodec.encode issued.ingress then
    match ← ApplicationDispatchAdmission.checkCurrent config.deployment config.profile
        ⟨config.federation, NativeHost.logicalHeight config durable⟩ config.signature
        durable ingress issued.ingress.spec issued.descriptor with
    | .error detail => return .error detail
    | .ok checked => return .ok ⟨issueBytesExact, checked⟩
  else return .error "dispatch issue ingress differs from admitted source"

end Minidregg.Kernel.ApplicationDispatchHistoricalCore
