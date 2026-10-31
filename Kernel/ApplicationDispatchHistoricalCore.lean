/-
Cycle-safe source evidence for app share issuance and current dispatch.
An `IssuedEvidence` proves one issue was natively admitted and its COMPLETE
intent equals an exact record. It does not prove that this record belongs to
the current admitted history. NativeHostReplay must mint that chronological
membership during its replay walk before a dispatch event can be admitted;
the upper live receiver uses the verifier-selected original prefix.
-/
module

public import Kernel.ApplicationDispatchPending
public import Kernel.ApplicationShareIssueReceiver
public import Kernel.ApplicationShareIssueGrainReceiver
public import Kernel.NativeHostContext

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic
import all Init.System.ST
import all Init.System.IO

@[expose] public section

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
  spec : ApplicationShareIssueSource.Spec
  ingressBytes : List UInt8
  descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry
  record : DurableReceiver.IntentRecord
  sourceExact :
    (∃ (pins : FactoryPins)
       (original : ResourceBirthController.Concrete.Durable)
       (directory : CredentialAuthorityDomainReceiver.LoadedDirectory original)
       (authority : CredentialAuthorityDomainReceiver.Loaded config.deployment original.snapshot)
       (height : Height)
       (ingress : ApplicationShareIssueSource.Ingress)
       (accepted : ApplicationShareIssueAdmission.Accepted config.profile config
         pins (.ofLoaded original directory authority) height ingress),
       spec = ingress.spec ∧
         ingressBytes = ApplicationShareIssueSource.ingressCodec.encode ingress ∧
         descriptor = accepted.birth.descriptor ∧
         record = DurableReceiver.IntentRecord.ofIntent
           (ApplicationShareIssueReceiver.intent accepted)) ∨
    (∃ (pins : FactoryPins)
       (original : ResourceBirthController.Concrete.Durable)
       (directory : CredentialAuthorityDomainReceiver.LoadedDirectory original)
       (authority : CredentialAuthorityDomainReceiver.Loaded config.deployment original.snapshot)
       (ambient : DeclaredResourceController.Ambient)
       (ingress : ApplicationShareIssueGrainSource.Ingress)
       (accepted : ApplicationShareIssueGrainAdmission.Accepted config.profile config
         pins (.ofLoaded original directory authority) ambient ingress),
       spec = ingress.spec ∧
         ingressBytes = ingress.canonicalBytes ∧
         descriptor = accepted.decoded.source.birth ∧
         record = DurableReceiver.IntentRecord.ofIntent
           (ApplicationShareIssueGrainReceiver.intent accepted))

/-- A bare ticket or event cannot call this factory: it needs the actual
private native Accepted issue and exact equality of all recorded intent
fields. The caller must separately prove chronological membership in an
admitted replay prefix before using this evidence for a dispatch. -/
def IssuedEvidence.fromAccepted (config : Config) (pins : FactoryPins)
    (original : ResourceBirthController.Concrete.Durable)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory original)
    (authority : CredentialAuthorityDomainReceiver.Loaded config.deployment original.snapshot)
    (height : Height)
    (ingress : ApplicationShareIssueSource.Ingress)
    (accepted : ApplicationShareIssueAdmission.Accepted config.profile config
      pins (.ofLoaded original directory authority) height ingress)
    (record : DurableReceiver.IntentRecord)
    (exact : record = DurableReceiver.IntentRecord.ofIntent
      (ApplicationShareIssueReceiver.intent accepted)) : IssuedEvidence config :=
  ⟨ingress.spec, ApplicationShareIssueSource.ingressCodec.encode ingress,
    accepted.birth.descriptor, record,
    Or.inl ⟨pins, original, directory, authority, height, ingress, accepted, rfl, rfl, rfl, exact⟩⟩

/-- The grain-backed issue is a separate admitted source with its own event22
and full joint birth intent. Its evidence is never constructed through the
legacy event15 accepted type. -/
def IssuedEvidence.fromGrainAccepted (config : Config) (pins : FactoryPins)
    (original : ResourceBirthController.Concrete.Durable)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory original)
    (authority : CredentialAuthorityDomainReceiver.Loaded config.deployment original.snapshot)
    (ambient : DeclaredResourceController.Ambient)
    (ingress : ApplicationShareIssueGrainSource.Ingress)
    (accepted : ApplicationShareIssueGrainAdmission.Accepted config.profile config
      pins (.ofLoaded original directory authority) ambient ingress)
    (record : DurableReceiver.IntentRecord)
    (exact : record = DurableReceiver.IntentRecord.ofIntent
      (ApplicationShareIssueGrainReceiver.intent accepted)) : IssuedEvidence config :=
  ⟨ingress.spec, ingress.canonicalBytes, accepted.decoded.source.birth, record,
    Or.inr ⟨pins, original, directory, authority, ambient, ingress, accepted, rfl, rfl, rfl, exact⟩⟩

def IssuedEvidence.transactionId {config : Config} (issued : IssuedEvidence config) : Digest :=
  issued.descriptor.transactionId

def IssuedEvidence.eventId {config : Config} (issued : IssuedEvidence config) : Digest :=
  issued.record.event.eventId

theorem IssuedEvidence.record_transaction {config : Config} (issued : IssuedEvidence config) :
    issued.record.transactionId = issued.transactionId := by
  rcases issued.sourceExact with
    ⟨_, _, _, _, _, _, accepted, _, _, descriptorExact, recordExact⟩ |
    ⟨_, _, _, _, _, _, accepted, _, _, descriptorExact, recordExact⟩
  · rw [recordExact]
    change (ApplicationShareIssueReceiver.intent accepted).transactionId =
      issued.descriptor.transactionId
    rw [descriptorExact]
    rfl
  · rw [recordExact]
    change (ApplicationShareIssueGrainReceiver.intent accepted).transactionId =
      issued.descriptor.transactionId
    rw [descriptorExact]
    rfl

theorem IssuedEvidence.record_event_bytes {config : Config} (issued : IssuedEvidence config) :
    issued.record.event.canonicalBytes = issued.ingressBytes := by
  rcases issued.sourceExact with
    ⟨_, _, _, _, _, _, accepted, _, ingressExact, _, recordExact⟩ |
    ⟨_, _, _, _, _, _, accepted, _, ingressExact, _, recordExact⟩
  · rw [recordExact, ingressExact]
    rfl
  · rw [recordExact, ingressExact]
    rfl

/-- Core selection is only a *current-image component*. The issue evidence
must be added to a verifier-minted chronological context before this candidate
can be committed or handed to a physical app. -/
structure CheckedCandidate (config : Config) (ground : DeclaredResourceController.Ground config.deployment)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (issued : IssuedEvidence config) where
  private mk ::
  issueBytesExact : ingress.issueIngressBytes = issued.ingressBytes
  checked : ApplicationDispatchAdmission.CheckedCurrent config.deployment config.profile
    ⟨config.federation, config.genesisHeight + ground.height⟩ ground ingress
    issued.spec issued.descriptor

/-- The dispatch names the issue's ingress bytes, the issued spec's installed
ticket is live at `ground`'s logical height under `config`, and the issuer
lineage is current over `ground` from the issue's own source bytes. -/
theorem CheckedCandidate.issuer_current {config : Config}
    {ground : DeclaredResourceController.Ground config.deployment}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    {issued : IssuedEvidence config}
    (candidate : CheckedCandidate config ground ingress issued) :
    ingress.issueIngressBytes = issued.ingressBytes ∧
      candidate.checked.ticket.liveAt (config.genesisHeight + ground.height) = true ∧
      issuerLineageCurrentFromSourceBytes config.deployment config.profile
        ⟨config.federation, config.genesisHeight + ground.height⟩ ground ingress issued.spec
        candidate.checked.selection
        (ApplicationShareIssueSource.sourceBytes issued.spec issued.descriptor)
        candidate.checked.prepared = true :=
  ⟨candidate.issueBytesExact, candidate.checked.ticketLive, candidate.checked.issuerCurrent⟩

def checkCurrent (config : Config) (ground : DeclaredResourceController.Ground config.deployment)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (issued : IssuedEvidence config) :
    IO (Except String (CheckedCandidate config ground ingress issued)) := do
  if issueBytesExact : ingress.issueIngressBytes = issued.ingressBytes then
    match ← ApplicationDispatchAdmission.checkCurrent config.deployment config.profile
        ⟨config.federation, config.genesisHeight + ground.height⟩ config.signature
        ground ingress issued.spec issued.descriptor with
    | .error detail => return .error detail
    | .ok checked => return .ok ⟨issueBytesExact, checked⟩
  else return .error "dispatch issue ingress differs from admitted source"

end Minidregg.Kernel.ApplicationDispatchHistoricalCore
