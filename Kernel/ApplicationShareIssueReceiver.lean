/-
One durable candidate intent for a special app-authorized ticket issue. This
is not wired to the native receiver or semantic replay yet. In particular a
bare resource birth with identical ticket bytes never implies this event.
-/
import Kernel.ApplicationShareIssueAdmission

namespace Minidregg.Kernel.ApplicationShareIssueReceiver
open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.ResourceCost
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.ApplicationShareIssueSource
open Minidregg.Kernel.ApplicationShareIssueAdmission
open Minidregg.Kernel.ApplicationShareIssueAtomicBirth
set_option autoImplicit false

variable {F : Type} [Field F] [DecidableEq F]
variable {profile : CanonicalRuntimeProfile.Profile F}
variable {config : NativeHost.Config} {pins : FactoryPins}
variable {durable : ResourceBirthController.Concrete.Durable} {height : Height}
variable {ingress : ApplicationShareIssueSource.Ingress}

/-- The complete canonical outer ingress, not a naked ticket payload, is the
event preimage. Historical use must still re-admit its two native branches at
the original verified prefix and compare the entire durable intent record. -/
def event (domain : Digest) (ingress : ApplicationShareIssueSource.Ingress) : StableEvent where
  codecVersion := 15
  domain := domain
  eventId := commitmentBytes
    ("DREGG/APPLICATION/SHARE-ISSUE-EVENT/v2".toUTF8.toList ++
      digestStream.encode domain ++ ingressCodec.encode ingress)
  canonicalBytes := ingressCodec.encode ingress

def issueNullifier (domain : Digest) (ingress : ApplicationShareIssueSource.Ingress)
    (descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry) : StableNullifier :=
  CredentialAuthorityReplay.nullifier domain (issueMarker ingress.spec descriptor)

def readGuards (accepted : Accepted profile config pins durable height ingress) :
    List ReadGuard :=
  ResourceBirthReceiver.readGuards accepted.birth ++
    ApplicationShareIssueDelegation.readGuards accepted.appPrepared

theorem readGuards_readonly (accepted : Accepted profile config pins durable height ingress)
    (guard : ReadGuard) (member : guard ∈ readGuards accepted) :
    guard.cellId ∉ accepted.birth.prepared.writes.map DataWrite.cellId := by
  rcases List.mem_append.mp member with birth | app
  · exact ResourceBirthReceiver.readGuards_readonly accepted.birth guard birth
  · exact accepted.appReadOnly guard app

theorem readGuards_exact (accepted : Accepted profile config pins durable height ingress)
    (guard : ReadGuard) (member : guard ∈ readGuards accepted) :
    guard.expectedRoot = durable.snapshot.model.roots guard.cellId := by
  rcases List.mem_append.mp member with birth | app
  · exact ResourceBirthReceiver.readGuards_exact accepted.birth guard birth
  · exact accepted.appChecked.guardsCurrent guard app

def writes (accepted : Accepted profile config pins durable height ingress) :
    List DataWrite := accepted.atomic.writes

theorem writes_unique (accepted : Accepted profile config pins durable height ingress) :
    ((writes accepted).map DataWrite.cellId).Nodup :=
  accepted.atomic.unique accepted.birth.prepared.writesUnique

theorem compositeGuards_readonly
    (accepted : Accepted profile config pins durable height ingress)
    (guard : ReadGuard) (member : guard ∈ readGuards accepted) :
    guard.cellId ∉ (writes accepted).map DataWrite.cellId :=
  accepted.atomic.readonly guard (readGuards_readonly accepted guard member)

theorem composite_roots_bound
    (accepted : Accepted profile config pins durable height ingress)
    (write : DataWrite) (member : write ∈ writes accepted) :
    ResourceBirthCodec.rootBytes write.canonicalPostBytes = write.exactPost :=
  accepted.atomic.roots_bound accepted.birth.prepared.write_roots_bound write member

/-- Charge includes the original empty resource birth, the full initialized
ticket post bytes, the extra signed app authority check, complete outer
ingress, and app read guard. Counting the entire final post is conservative;
the accepted birth fee remains the only Book debit. -/
def charge (accepted : Accepted profile config pins durable height ingress) : Charge
  | .incidences => ResourceBirthReceiver.charge accepted.birth .incidences + 1
  | .turnBytes => ResourceBirthReceiver.charge accepted.birth .turnBytes +
      (ingressCodec.encode ingress).length +
      (initializedWrite accepted.sourceReady).canonicalPostBytes.length
  | .memoryTouches => ResourceBirthReceiver.charge accepted.birth .memoryTouches + 1
  | .witnessBytes => ResourceBirthReceiver.charge accepted.birth .witnessBytes +
      ingress.appEnvelope.length +
      (initializedWrite accepted.sourceReady).canonicalPostBytes.length
  | .proofWork => ResourceBirthReceiver.charge accepted.birth .proofWork + 1
  | .storageBytes => ResourceBirthReceiver.charge accepted.birth .storageBytes +
      (ingressCodec.encode ingress).length +
      (initializedWrite accepted.sourceReady).canonicalPostBytes.length
  | .sideEffectCount => ResourceBirthReceiver.charge accepted.birth .sideEffectCount + 1
  | .feeDebit => ResourceBirthReceiver.charge accepted.birth .feeDebit
  | .networkBytes | .leaseByteBlocks => 0

theorem charge_fee_exact (accepted : Accepted profile config pins durable height ingress) :
    charge accepted .feeDebit = accepted.birth.descriptor.fee.amount := rfl

theorem charge_fee_source_quoted (accepted : Accepted profile config pins durable height ingress) :
    charge accepted .feeDebit = accepted.birth.descriptor.quotedFee
      (accepted.sourceReady.effectiveTariff config.tariff) := by
  rw [charge_fee_exact]
  exact accepted.special_fee_bound

/-- The special event and nullifier distinguish this composite issue from an
ordinary resource birth. Both prior-image admissions were checked at the same
`durable`; the app read guard fences its cell root, while the birth's complete
authority guards and the full-image CAS fence current policy/grant state. The
newborn owner/control grants go to the issuer; a participant still needs an
actual native observe delegation before dispatch can use its ticket selector. -/
def intent (accepted : Accepted profile config pins durable height ingress) :
    DataIntent ResourceBirthCodec.rootBytes where
  transactionId := accepted.birth.descriptor.transactionId
  writes := writes accepted
  readGuards := readGuards accepted
  nullifiers := ResourceBirthReceiver.birthNullifier config.deployment.domain
      accepted.birth.descriptor.authorityNullifier ::
    [issueNullifier config.deployment.domain ingress accepted.birth.descriptor]
  exactCharge := charge accepted
  event := event config.deployment.domain ingress
  subject := some accepted.birth.descriptor.creator
  postRootsBound := composite_roots_bound accepted
  guardsReadOnly := compositeGuards_readonly accepted

theorem intent_event_version (accepted : Accepted profile config pins durable height ingress) :
    (intent accepted).event.codecVersion = 15 := rfl

theorem intent_retains_outer (accepted : Accepted profile config pins durable height ingress) :
    (intent accepted).event.canonicalBytes = ingressCodec.encode ingress := rfl

structure Receipt where
  transactionId : Digest
  eventId : Digest
  deriving DecidableEq, Repr

inductive Result where
  | confirmed (kind : DurableReceiverIO.Confirmation) (receipt : Receipt)
  | historical (receipt : Receipt)
  | rejected (reason : String)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def receipt (domain : Digest) (ingress : ApplicationShareIssueSource.Ingress)
    (birth : ResourceBirthPolicyController.Concrete.DecodedIngress) : Receipt :=
  ⟨birth.descriptor.transactionId, (event domain ingress).eventId⟩

/-- This selector is used only after a verified native reopen. It recovers an
exact previously accepted issue when the issuer's current delegation has since
expired; it never submits missing work. The replay verifier must have admitted
event 15 at the original prefix and checked the complete recorded intent. -/
def replay (durable : ResourceBirthController.Concrete.Durable) (domain : Digest)
    (ingress : ApplicationShareIssueSource.Ingress)
    (birth : ResourceBirthPolicyController.Concrete.DecodedIngress) :
    Option (Except String Receipt) :=
  match Snapshot.lookupRecorded birth.descriptor.transactionId durable.snapshot.model.journal with
  | none => none
  | some recorded =>
      if recorded.transactionId = birth.descriptor.transactionId ∧
          recorded.event.event = event domain ingress ∧
          recorded.nullifiers =
            [ResourceBirthReceiver.birthNullifier domain birth.descriptor.authorityNullifier,
              issueNullifier domain ingress birth.descriptor] then
        some (.ok (receipt domain ingress birth))
      else some (.error "share issue transaction identity conflict")

/-- Fresh work must pass both current native branches at one loaded image,
then the ordinary durable prepare/charge/journal/CAS. No host Boolean can
construct `Accepted` or the emitted intent. -/
def receiveLoaded (config : NativeHost.Config) (pins : FactoryPins)
    (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport)
    (durable : ResourceBirthController.Concrete.Durable) (height : Height)
    (bytes : List UInt8) : IO Result := do
  let some outer := ingressCodec.decode bytes
    | return .rejected "noncanonical share issue ingress"
  let some birth := ResourceBirthPolicyController.Concrete.decodeIngress outer.birthIngress
    | return .rejected "noncanonical share issue birth ingress"
  match replay durable config.deployment.domain outer birth with
  | some (.ok historical) => return .historical historical
  | some (.error reason) => return .rejected reason
  | none =>
      match ← ApplicationShareIssueAdmission.admitNative config.profile config pins
          native durable height bytes with
      | .error reason => return .rejected reason
      | .ok ⟨acceptedIngress, accepted⟩ =>
          match ← DurableReceiverIO.receiveLoaded transport ResourceBirthCodec.rootBytes
              durable (intent accepted) with
          | .confirmed kind _ =>
              return .confirmed kind
                ⟨accepted.birth.descriptor.transactionId,
                  (event config.deployment.domain acceptedIngress).eventId⟩
          | .rejected _ => return .rejected "durable share issue refused"
          | .contention => return .contention
          | .unavailable detail => return .unavailable detail
          | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.ApplicationShareIssueReceiver
