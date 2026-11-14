/- One fleet turn publishes its Book postings, its optional topic append (the
stream head and one fresh entry cell) and its operation marker in one CAS, with
the pinned tariff as the exact fee lane. -/
module

public import Kernel.FleetTurn

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

namespace Minidregg.Kernel.FleetTurnReceiver

open Minidregg.Compiler
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.FleetTurn
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

def transactionId (domain semantics : Digest) (ingress : DecodedIngress) : Digest :=
  ⟨marker domain semantics ingress.command⟩

def eventId (domain semantics : Digest) (ingress : DecodedIngress) : Digest :=
  effectDigest domain semantics ingress.command

/-- The replay envelope is the complete signed ingress, so the payload of a
topic event is recoverable from the accepted journal by transaction id. -/
def event (domain semantics : Digest) (ingress : DecodedIngress) : StableEvent where
  codecVersion := 1
  domain := domain
  eventId := eventId domain semantics ingress
  canonicalBytes := ingress.bytes

def nullifier (domain semantics : Digest) (ingress : DecodedIngress) : StableNullifier :=
  CredentialAuthorityReplay.nullifier domain (marker domain semantics ingress.command)

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {tariff : CreationTariff} {ambient : Ambient}
  {ground : ServedBasis.Ground deployment} {command : Command}

def bookWrite (prepared : Prepared deployment profile tariff ambient ground command) : DataWrite :=
  ResourceBirthController.Concrete.packedWrite deployment.resourceBookId
    ⟨.resourceBook, prepared.book.payload⟩ ⟨.resourceBook, prepared.resources.post⟩

def topicWrites (prepared : Prepared deployment profile tariff ambient ground command) :
    List DataWrite :=
  prepared.topic.toList.flatMap TopicPlan.writes

def writes (prepared : Prepared deployment profile tariff ambient ground command) : List DataWrite :=
  bookWrite prepared :: topicWrites prepared

/-- All authenticated law heads, pinned predecessors and structural roots.
PhysicalShape requires successful resolution before getD can supply any guards. -/
def sourceGuards (prepared : Prepared deployment profile tariff ambient ground command) :
    List ReadGuard :=
  ((lawReadGuards prepared).getD []).map fun guard => ⟨⟨guard.1⟩, guard.2⟩

def readGuards (prepared : Prepared deployment profile tariff ambient ground command) :
    List ReadGuard :=
  let written := (writes prepared).map DataWrite.cellId
  (sourceGuards prepared ++ ground.authorityReadGuards).filter fun guard =>
    guard.cellId ∉ written

def PhysicalShape (prepared : Prepared deployment profile tariff ambient ground command) : Prop :=
  ((writes prepared).map DataWrite.cellId).Nodup ∧
    (∀ write ∈ writes prepared, write.expectedPre = ground.view.model.roots write.cellId) ∧
    (∀ write ∈ writes prepared, ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
    (lawReadGuards prepared).isSome = true ∧
    (∀ guard ∈ sourceGuards prepared ++ ground.authorityReadGuards,
      guard.expectedRoot = ground.view.model.roots guard.cellId)

instance physicalShapeDecidable
    (prepared : Prepared deployment profile tariff ambient ground command) :
    Decidable (PhysicalShape prepared) := by
  unfold PhysicalShape
  infer_instance

theorem writes_roots_bound (prepared : Prepared deployment profile tariff ambient ground command)
    (write : DataWrite) (member : write ∈ writes prepared) :
    rootBytes write.canonicalPostBytes = write.exactPost := by
  rcases List.mem_cons.mp member with rfl | rest
  · rfl
  · obtain ⟨plan, _, inPlan⟩ := List.mem_flatMap.mp rest
    simp only [TopicPlan.writes, List.mem_cons, List.not_mem_nil, or_false] at inPlan
    rcases inPlan with rfl | rfl
    · exact StreamWrite.headWrite_root _ _ _
    · exact StreamWrite.entryWrite_root _

theorem readGuards_readonly (prepared : Prepared deployment profile tariff ambient ground command)
    (shape : PhysicalShape prepared) (guard : ReadGuard) (member : guard ∈ readGuards prepared) :
    guard.cellId ∉ (writes prepared).map DataWrite.cellId := by
  exact of_decide_eq_true (List.mem_filter.mp member).2

structure AcceptedTurn [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (tariff : CreationTariff) (ambient : Ambient)
    (ground : ServedBasis.Ground deployment) (ingress : DecodedIngress) where
  private mk ::
  prepared : Prepared deployment profile tariff ambient ground ingress.command
  accepted : FleetTurn.Accepted prepared ingress
  physical : PhysicalShape prepared
theorem AcceptedTurn.sound [DecidableEq F] {ingress : DecodedIngress}
    (accepted : AcceptedTurn deployment profile tariff ambient ground ingress) :
    accepted.accepted.receipt.envelopeBytes = ingress.ingress.envelope ∧
    CanonicalResourceKernel.AcceptedBatch accepted.prepared.book.payload
      (batch tariff ingress.command) ∧
    PhysicalShape accepted.prepared :=
  ⟨accepted.accepted.envelopeExact, accepted.prepared.resources, accepted.physical⟩

def admitDecodedNative [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (tariff : CreationTariff) (ambient : Ambient)
    (ground : ServedBasis.Ground deployment) (native : CredentialSignatureIO.NativeConfig)
    (ingress : DecodedIngress) :
    IO (Except Reject (AcceptedTurn deployment profile tariff ambient ground ingress)) := do
  match prepare deployment profile tariff ambient ground ingress.command with
  | .error reason => return .error reason
  | .ok prepared =>
    if physical : PhysicalShape prepared then
      match ← admitNative native prepared ingress with
      | .error reason => return .error reason
      | .ok accepted => return .ok ⟨prepared, accepted, physical⟩
    else return .error .physicalPreparation

variable [DecidableEq F] {ingress : DecodedIngress}

/-- `feeDebit` is the exact Book fee posted to the collector. -/
def charge (accepted : AcceptedTurn deployment profile tariff ambient ground ingress) :
    ResourceCost.Charge
  | .incidences => 1
  | .turnBytes => ingress.bytes.length
  | .memoryTouches => (writes accepted.prepared).length + (readGuards accepted.prepared).length
  | .storageBytes => DeployedCharge.storageCharge ground.view
      (writes accepted.prepared)
      (event deployment.domain profile.semantics ingress)
  | .witnessBytes => ingress.ingress.envelope.length
  | .proofWork => 1
  | .feeDebit => ingress.command.fee
  | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

def intent (accepted : AcceptedTurn deployment profile tariff ambient ground ingress) :
    DataIntent rootBytes where
  transactionId := transactionId deployment.domain profile.semantics ingress
  subject := some ingress.command.subject
  writes := writes accepted.prepared
  readGuards := readGuards accepted.prepared
  nullifiers := [nullifier deployment.domain profile.semantics ingress]
  exactCharge := (Minidregg.Theory.ResourceCost.Charge.materialize (charge accepted)).toCharge
  event := event deployment.domain profile.semantics ingress
  postRootsBound := writes_roots_bound accepted.prepared
  guardsReadOnly := readGuards_readonly accepted.prepared accepted.physical

structure Receipt where
  transactionId : Digest
  eventId : Digest
  deriving DecidableEq, Repr

def receipt (domain semantics : Digest) (ingress : DecodedIngress) : Receipt :=
  ⟨transactionId domain semantics ingress, (event domain semantics ingress).eventId⟩

/-- A recorded intent is exactly this ingress's: its transaction id, its event (the whole
signed ingress) and its one nullifier. -/
def exactRecord (domain semantics : Digest) (ingress : DecodedIngress)
    (recorded : DurableCommitProtocol.Intent TransactionId CellId StableNullifier ReplayEnvelope) : Bool :=
  decide (recorded.transactionId = transactionId domain semantics ingress ∧
    recorded.event.event = event domain semantics ingress ∧
    recorded.nullifiers = [nullifier domain semantics ingress])

/-- The keys a turn consults beyond the state: its transaction id (replay detection,
`replayOn`) and its operation marker's nullifier (`FleetTurn.Prepared.unspent`). A light
basis for a turn declares these. -/
def turnKeys (domain semantics : Digest) (ingress : DecodedIngress) : DurableView.Keys :=
  ⟨[transactionId domain semantics ingress], [nullifier domain semantics ingress]⟩

/-- The replay verdict on a ground, read only through its answer for the turn's transaction
id (`ServedBasis.Ground.replayOf`): one journal read on the light route. -/
def replayOn (domain semantics : Digest) (ground : ServedBasis.Ground deployment)
    (ingress : DecodedIngress) : ServedBasis.Ground.Replay Receipt :=
  ground.replayOf (transactionId domain semantics ingress) (exactRecord domain semantics ingress)
    (receipt domain semantics ingress)

inductive Result where
  | confirmed (kind : DurableReceiverIO.Confirmation) (receipt : Receipt)
  | rejected (reason : Reject)
  | transactionConflict
  | durableRejected (reason : DurableDataIntent.RejectReason)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

/-- **The light fleet receive.** The turn's keys (`turnKeys`) are read from the authenticated
history into a basis (`basisOf`, the light opening's `Light.basisVia`); the replay check, the
preparation and the admission run on `Ground.ofBasis`; the commit is
`DurableServed.receiveServed` on the light opening. Nothing opens the full materialization.
The admission height is `genesisHeight + basis.height`. -/
def receiveServed (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (tariff : CreationTariff) (federation : FederationId) (genesisHeight : Nat)
    (native : CredentialSignatureIO.NativeConfig) (transport : DurableReceiverIO.Transport)
    (opening : DurableServed.Opening rootBytes)
    (basisOf : DurableView.Keys →
      IO (Except String (ServedBasis.Basis deployment opening.store)))
    (bytes : List UInt8)
    (adopt : (next : DurableServed.Opening rootBytes) → (written : List DurableDataIntent.CellId) →
      DurableServed.Served.Moved opening.served next.served written →
      Option CredentialAuthorityServed.HeldCell → IO Unit :=
      fun _ _ _ _ => pure ()) : IO Result := do
  let some ingress := decodeIngress bytes
    | return .rejected .malformedIngress
  match ← basisOf (turnKeys deployment.domain profile.semantics ingress) with
  | .error detail => return .unavailable detail
  | .ok basis =>
      let ground : ServedBasis.Ground deployment := .ofBasis basis
      match replayOn deployment.domain profile.semantics ground ingress with
      | .original prior => return .confirmed .replayed prior
      | .conflict => return .transactionConflict
      | .undeclared => return .unavailable "the basis does not answer for the turn's transaction id"
      | .fresh =>
          match ← admitDecodedNative deployment profile tariff
              ⟨federation, genesisHeight + basis.height⟩ ground native ingress with
          | .error reason => return .rejected reason
          | .ok accepted =>
              let issued := receipt deployment.domain profile.semantics ingress
              match ← DurableServed.receiveServed transport rootBytes opening (intent accepted) with
              | .appended kind next _ _ _ _ moved => do adopt next _ moved none; return .confirmed kind issued
              | .replayed _ => return .confirmed .replayed issued
              | .rejected reason => return .durableRejected reason
              | .contention => return .contention
              | .unavailable detail => return .unavailable detail
              | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.FleetTurnReceiver
