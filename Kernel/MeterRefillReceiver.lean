/-
# Kernel.MeterRefillReceiver — the controller refills the seed meter (M2)

The commit protocol's meter (`DurableCommitProtocol.Snapshot.available`) is not a cell: every
admitted record debits it (`preflight`, `insufficientBudget`). This receiver is the one
family that raises it. Its intent writes no cell, claims one tagged nullifier, charges
nothing and carries the refill's amount as `credit`, which the extended install adds back
(`Snapshot.install`, `PlatformCell.protocol_install_matches`). A zero charge is funded by an
exhausted meter (`PlatformCell.refill_funded_at_exhaustion`), so a refill is admitted when
the meter is spent.

Authorization (the deployed M2-c, `AcceptedRefill.sound`):
* the sponsor IS the controller the platform cell names (`PlatformCellLayout.controllerOf`,
  written at genesis and never changed, `Reachable.controller_stays`): holding the control
  capability is not enough, so a delegate cannot refill;
* the sponsor's signature verifies under its current enrolled key over the request
  (`CredentialSignatureAdmission.verifyNative`, the deployment's native verifier);
* the sponsor presents the control (program) capability on the factory, verb
  `installPolicy`, checked as capability evidence in capability mode
  (`capabilityEvidenceCheckedFor` under `sourceCapabilityPortal`: holder, scope, window,
  native use, membership and revocation);
* the single-use marker of (domain, semantics, sponsor, nonce) is unspent.

The authority cell is the CAS read guard: a revocation of the controller's capability, or
any other authority change, between plan and commit makes the refill stale. The meter is
unbounded by design (`PlatformCell`'s header), so no fit bound applies.
-/
module

public import Compiler.DurableReceiverIO
public import Kernel.CapabilityRevocationController
public import Kernel.PlatformCellDomain
public import Kernel.PlatformCell
public import Kernel.PayTariff

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

namespace Minidregg.Kernel.MeterRefillReceiver

open Minidregg.Compiler
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.CredentialAuthorityEntryCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.PlatformCellLayout (controllerOf)
open Minidregg.Kernel.PayTariff (framed framed_canonical)
open Minidregg.Theory
open Minidregg.Theory.CredentialAuthorityEffects
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev Snapshot := CredentialAuthorityDomain.Snapshot

/-! ## Command and ingress -/

structure Command where
  sponsor : SubjectId
  control : CapabilityId
  expectedAuthorityRoot : Digest
  nonce : Nat
  amount : ResourceCost.Charge

def commandStream : StreamCodec Command :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product capabilityIdStream
        (StreamCodec.product digestStream
          (StreamCodec.product StreamCodec.nat DurableReceiverCodec.chargeStream))))
    (fun c => (c.sponsor, c.control, c.expectedAuthorityRoot, c.nonce, c.amount))
    (fun (sponsor, control, authorityRoot, nonce, amount) =>
      ⟨sponsor, control, authorityRoot, nonce, amount⟩)
    (by intro c; cases c; rfl)

def commandFrame : List UInt8 := "DREGG/METER/REFILL/v1".toUTF8.toList

def commandCodec : LawfulCodec Command := framed commandFrame commandStream

theorem command_roundtrip (command : Command) :
    commandCodec.decode (commandCodec.encode command) = some command :=
  commandCodec.decode_encode command

theorem commandCodec_injective {a b : Command} (same : commandCodec.encode a = commandCodec.encode b) :
    a = b :=
  PlatformCell.lawful_injective commandCodec same

/-- The signed ingress: the command bytes and the sponsor's envelope over the request. -/
structure Ingress where
  commandBytes : List UInt8
  sponsorEnvelope : List UInt8
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap (StreamCodec.product bytesStream bytesStream)
    (fun ingress => (ingress.commandBytes, ingress.sponsorEnvelope))
    (fun (command, sponsor) => ⟨command, sponsor⟩)
    (by intro ingress; cases ingress; rfl)

def ingressCodec : LawfulCodec Ingress :=
  framed "DREGG/METER/REFILL/SIGNED/v1".toUTF8.toList ingressStream

structure DecodedIngress where
  private mk ::
  ingress : Ingress
  command : Command
  canonical : commandCodec.encode command = ingress.commandBytes
  envelope : CredentialSignedEnvelopeController.SignedEnvelope
  envelopeExact : CredentialSignatureAdmission.canonicalEnvelopeCodec.decode ingress.sponsorEnvelope =
    some envelope

theorem DecodedIngress.sound (decoded : DecodedIngress) :
    commandCodec.encode decoded.command = decoded.ingress.commandBytes ∧
      CredentialSignatureAdmission.canonicalEnvelopeCodec.decode decoded.ingress.sponsorEnvelope =
        some decoded.envelope :=
  ⟨decoded.canonical, decoded.envelopeExact⟩

def decodeIngress (bytes : List UInt8) : Option DecodedIngress := do
  let ingress ← ingressCodec.decode bytes
  match commandExact : commandCodec.decode ingress.commandBytes with
  | none => none
  | some command =>
    match envelopeExact : CredentialSignatureAdmission.canonicalEnvelopeCodec.decode
        ingress.sponsorEnvelope with
    | none => none
    | some envelope =>
      some ⟨ingress, command, framed_canonical commandFrame commandStream commandExact,
        envelope, envelopeExact⟩

def DecodedIngress.bytes (ingress : DecodedIngress) : List UInt8 :=
  ingressCodec.encode ingress.ingress

/-- The single-use marker: one per (sponsor, nonce) in a deployment and semantics, under a
customization no other family uses (the family tag of `PlatformCell.Nullifier`). -/
def marker (domain semantics : Digest) (command : Command) : Nat :=
  (Sp800185Cshake256.hash "DREGG.METER.REFILL.IDENTITY/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
        StreamCodec.nat))).encode
      (domain, semantics, command.sponsor, command.nonce))).digest.value

/-! ## The request the controller signs -/

def effectDigest (domain semantics : Digest) (command : Command) : Digest :=
  (Sp800185Cshake256.hash "DREGG.METER.REFILL.EFFECT/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream)).encode
      (domain, semantics, commandCodec.encode command))).digest

structure Ambient where
  federation : FederationId
  height : Height

def context (deployment : Deployment) (snapshot : Snapshot) (semantics : Digest)
    (ambient : Ambient) (command : Command) : RequestContext where
  authority :=
    { kind := .program
      domain := snapshot.domain
      semantics := semantics
      federation := ambient.federation
      subject := command.sponsor
      subjectKeyEpoch := snapshot.authState.subjectKeyEpoch command.sponsor
      target := ⟨deployment.factoryId⟩
      verb := .installPolicy
      nonce := marker snapshot.domain semantics command
      height := ambient.height
      policyId := ⟨deployment.factoryId⟩
      policyEpoch := snapshot.authState.policyEpoch ⟨deployment.factoryId⟩
      policyRevision := snapshot.authState.policyRevision ⟨deployment.factoryId⟩
      cost := (commandCodec.encode command).length }
  argsDigestBytes := fun bytes =>
    (Sp800185Cshake256.hash "DREGG.METER.REFILL.ARGS/v1".toUTF8.toList
      (commandCodec.encode command ++ bytes)).digest

/-- The request: the command under the authority cell's root, so the signature binds the
amount, the nonce and the authority state it was planned on. -/
def request (deployment : Deployment) (snapshot : Snapshot) (semantics : Digest)
    (ambient : Ambient) (command : Command) : Request .program :=
  ((context deployment snapshot semantics ambient command).request commandCodec
    (effectDigest snapshot.domain semantics) snapshot.cell.root
    (marker snapshot.domain semantics command) command).2

/-! ## Preparation and admission -/

inductive Reject where
  | malformedIngress | authorityUnavailable | platformUnavailable | staleAuthority
  | notController | replayedMarker | capabilityRejected
  | signature (reason : CredentialSignatureAdmission.Reject)
  deriving DecidableEq, Repr

def requireSome {A : Type} (reason : Reject) : Option A → Except Reject A
  | none => .error reason
  | some value => .ok value

structure Prepared (deployment : Deployment) (semantics : Digest) (durable : Durable)
    (command : Command) where
  private mk ::
  authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot
  platform : PlatformCellDomain.Loaded deployment durable.snapshot
  /-- The sponsor is the controller the platform cell names. -/
  controller : controllerOf platform.cell.logical = some command.sponsor
  /-- The signed command names the authority state it is admitted against. -/
  authorityCurrent : command.expectedAuthorityRoot = authority.snapshot.cell.root
  fresh : authority.snapshot.spent (marker authority.snapshot.domain semantics command) = false

def prepare (deployment : Deployment) (semantics : Digest) (durable : Durable) (command : Command) :
    Except Reject (Prepared deployment semantics durable command) := do
  let authority ← requireSome .authorityUnavailable (readDeployment deployment durable)
  let platform ← requireSome .platformUnavailable (PlatformCellDomain.load deployment durable.snapshot)
  if controller : controllerOf platform.cell.logical = some command.sponsor then
    if authorityCurrent : command.expectedAuthorityRoot = authority.snapshot.cell.root then
      if fresh : authority.snapshot.spent (marker authority.snapshot.domain semantics command) = false then
        pure ⟨authority, platform, controller, authorityCurrent, fresh⟩
      else throw .replayedMarker
    else throw .staleAuthority
  else throw .notController

variable {deployment : Deployment} {semantics : Digest} {durable : Durable} {command : Command}

/-- The prepared refill's guarantee: the sponsor is the controller the loaded platform cell
names, the command names the loaded authority's root, and its marker is unspent there. -/
theorem Prepared.sound (prepared : Prepared deployment semantics durable command) :
    controllerOf prepared.platform.cell.logical = some command.sponsor ∧
      command.expectedAuthorityRoot = prepared.authority.snapshot.cell.root ∧
      prepared.authority.snapshot.spent
        (MeterRefillReceiver.marker prepared.authority.snapshot.domain semantics command) = false :=
  ⟨prepared.controller, prepared.authorityCurrent, prepared.fresh⟩

def Prepared.request (prepared : Prepared deployment semantics durable command) (ambient : Ambient) :
    Request .program :=
  MeterRefillReceiver.request deployment prepared.authority.snapshot semantics ambient command

def Prepared.marker (prepared : Prepared deployment semantics durable command) : Nat :=
  MeterRefillReceiver.marker prepared.authority.snapshot.domain semantics command

/-- An admitted refill: the sponsor's verified signature over the request, and the control
capability on the factory checked as capability evidence for that request. -/
structure Accepted (prepared : Prepared deployment semantics durable command) (ambient : Ambient)
    (ingress : DecodedIngress) where
  private mk ::
  receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot
  envelopeExact : receipt.envelopeBytes = ingress.ingress.sponsorEnvelope
  evidence : { evidence : Evidence (sourceCapabilityPortal prepared.authority.snapshot prepared.marker)
      prepared.authority.snapshot.authState (prepared.request ambient) //
    NamesStored prepared.authority.snapshot command.control evidence }

def admitNative (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared deployment semantics durable command) (ambient : Ambient)
    (ingress : DecodedIngress) : IO (Except Reject (Accepted prepared ambient ingress)) := do
  match ← CredentialSignatureAdmission.verifyNative native prepared.authority.snapshot
      prepared.marker (prepared.request ambient) ingress.ingress.sponsorEnvelope with
  | .error reason => return .error (.signature reason)
  | .ok receipt =>
      if same : receipt.envelopeBytes = ingress.ingress.sponsorEnvelope then
        match capabilityEvidenceCheckedFor prepared.authority.snapshot
            (sourceCapabilityPortal prepared.authority.snapshot prepared.marker)
            (prepared.request ambient) command.control () receipt () (fun _ => ())
            (fun id => .capability .program id) with
        | .error _ => return .error .capabilityRejected
        | .ok evidence => return .ok ⟨receipt, same, evidence⟩
      else return .error .capabilityRejected

/-- The exact header the controller signs, derived from the current authority. -/
def signingHeader (deployment : Deployment) (semantics : Digest) (ambient : Ambient)
    (durable : Durable) (command : Command) :
    Except String CredentialSignedEnvelopeController.SignedHeader := do
  let some authority := readDeployment deployment durable
    | .error "authority unavailable"
  (CredentialSignatureAdmission.signingHeader authority.snapshot
    (MeterRefillReceiver.marker deployment.domain semantics command)
    ⟨.program, MeterRefillReceiver.request deployment authority.snapshot semantics ambient command⟩).mapError
      (fun reason => s!"meter-refill signer key: {repr reason}")

/-! ## The intent -/

def transactionId (domain semantics : Digest) (ingress : DecodedIngress) : Digest :=
  ⟨marker domain semantics ingress.command⟩

def event (domain _semantics : Digest) (ingress : DecodedIngress) : StableEvent where
  codecVersion := 1
  domain := domain
  eventId := (Sp800185Cshake256.hash "DREGG.METER.REFILL.EVENT/v1".toUTF8.toList ingress.bytes).digest
  canonicalBytes := ingress.bytes

def nullifier (domain semantics : Digest) (ingress : DecodedIngress) : StableNullifier :=
  CredentialAuthorityReplay.nullifier domain (marker domain semantics ingress.command)

structure AcceptedRefill (deployment : Deployment) (semantics : Digest) (ambient : Ambient)
    (durable : Durable) (ingress : DecodedIngress) where
  private mk ::
  prepared : Prepared deployment semantics durable ingress.command
  accepted : MeterRefillReceiver.Accepted prepared ambient ingress

def admitDecodedNative (deployment : Deployment) (semantics : Digest) (ambient : Ambient)
    (durable : Durable) (native : CredentialSignatureIO.NativeConfig) (ingress : DecodedIngress) :
    IO (Except Reject (AcceptedRefill deployment semantics ambient durable ingress)) := do
  match prepare deployment semantics durable ingress.command with
  | .error reason => return .error reason
  | .ok prepared =>
      match ← admitNative native prepared ambient ingress with
      | .error reason => return .error reason
      | .ok accepted => return .ok ⟨prepared, accepted⟩

variable {ambient : Ambient} {ingress : DecodedIngress}

/-- The admitted refill's guarantee: the checked signature's envelope is the ingress's sponsor
envelope, and the control capability evidence names a stored capability. -/
theorem Accepted.sound {prepared : Prepared deployment semantics durable command}
    (accepted : Accepted prepared ambient ingress) :
    accepted.receipt.envelopeBytes = ingress.ingress.sponsorEnvelope ∧
      NamesStored prepared.authority.snapshot command.control accepted.evidence.1 :=
  ⟨accepted.envelopeExact, accepted.evidence.2⟩

/-- The refill's intent (`PlatformCell.Refill.intent` on the protocol): no write, the
authority cell as its guard, one tagged nullifier, no charge, the amount as credit. -/
def intent (accepted : AcceptedRefill deployment semantics ambient durable ingress) :
    DataIntent rootBytes where
  transactionId := transactionId deployment.domain semantics ingress
  subject := some ingress.command.sponsor
  writes := []
  readGuards := accepted.prepared.authority.readGuards
  nullifiers := [nullifier deployment.domain semantics ingress]
  exactCharge := 0
  event := event deployment.domain semantics ingress
  credit := ingress.command.amount
  postRootsBound := by intro write member; cases member
  guardsReadOnly := by intro guard _; simp

/-- **Keystone M2-c, deployed: an accepted refill.** Its sponsor is the
controller the platform cell names; the sponsor's signature verified over the request; the
control capability on the factory is the capability evidence of that request; the marker
was unspent; and the committed intent writes nothing, charges nothing, claims exactly its
marker's nullifier and credits exactly the signed amount, with the authority cell's exact
root as its guard. -/
theorem AcceptedRefill.sound (accepted : AcceptedRefill deployment semantics ambient durable ingress) :
    controllerOf accepted.prepared.platform.cell.logical = some ingress.command.sponsor ∧
      accepted.accepted.receipt.envelopeBytes = ingress.ingress.sponsorEnvelope ∧
      NamesStored accepted.prepared.authority.snapshot ingress.command.control
        accepted.accepted.evidence.val ∧
      accepted.prepared.authority.snapshot.spent accepted.prepared.marker = false ∧
      (intent accepted).writes = [] ∧
      (intent accepted).exactCharge = 0 ∧
      (intent accepted).nullifiers = [nullifier deployment.domain semantics ingress] ∧
      (intent accepted).credit = ingress.command.amount ∧
      (∀ guard ∈ (intent accepted).readGuards,
        guard.expectedRoot = durable.snapshot.model.roots guard.cellId) :=
  ⟨accepted.prepared.controller, accepted.accepted.envelopeExact, accepted.accepted.evidence.property,
    accepted.prepared.fresh, rfl, rfl, rfl, rfl,
    fun guard member => accepted.prepared.authority.readGuards_exact guard member⟩

/-- **Teeth (replay).** No refill is accepted on an image whose marker nullifier is already
consumed. -/
theorem spent_empty
    (spent : durable.snapshot.model.consumed (nullifier deployment.domain semantics ingress) = true) :
    IsEmpty (AcceptedRefill deployment semantics ambient durable ingress) := by
  refine ⟨fun accepted => ?_⟩
  have fresh := accepted.prepared.fresh
  rw [accepted.prepared.authority.spentExact, accepted.prepared.authority.domainExact] at fresh
  unfold CredentialAuthorityDomainReceiver.spentOf at fresh
  unfold nullifier at spent
  rw [spent] at fresh
  cases fresh

/-- **Teeth (forgery by a delegate).** No refill is accepted whose sponsor is not the
controller the image's platform cell names, whatever capability it presents. -/
theorem notController_empty
    (other : ((PlatformCellDomain.load deployment durable.snapshot).bind
      fun loaded => controllerOf loaded.cell.logical) ≠ some ingress.command.sponsor) :
    IsEmpty (AcceptedRefill deployment semantics ambient durable ingress) := by
  refine ⟨fun accepted => other ?_⟩
  obtain ⟨found, loaded, same⟩ := PlatformCellDomain.load_exact deployment durable.snapshot
    accepted.prepared.platform.cell accepted.prepared.platform.observed
  rw [loaded]
  show controllerOf found.cell.logical = some ingress.command.sponsor
  rw [same]
  exact accepted.prepared.controller

/-- The committed meter of an accepted refill is the spec's `refilled`: the extended
install of its intent raises every lane by the amount and spends its nullifier
(`PlatformCell.refilled_is_deployed_install`). -/
theorem intent_install_refilled (accepted : AcceptedRefill deployment semantics ambient durable ingress)
    (before : DurableCommitProtocol.Snapshot TransactionId CellId StableNullifier ReplayEnvelope) :
    (DurableCommitProtocol.Snapshot.install before (intent accepted).erase).available =
      fun lane => before.available lane + ingress.command.amount lane := by
  funext lane
  simp [DurableCommitProtocol.Snapshot.install, intent, DataIntent.erase]

/-! ## The receiver -/

structure Receipt where
  transactionId : Digest
  eventId : Digest
  deriving DecidableEq, Repr

def receipt (domain semantics : Digest) (ingress : DecodedIngress) : Receipt :=
  ⟨transactionId domain semantics ingress, (event domain semantics ingress).eventId⟩

def replay (domain semantics : Digest) (durable : Durable) (ingress : DecodedIngress) :
    Option (Except Unit Receipt) :=
  match DurableCommitProtocol.Snapshot.lookupRecorded
      (transactionId domain semantics ingress) durable.snapshot.model.journal with
  | none => none
  | some recorded =>
    if recorded.transactionId = transactionId domain semantics ingress ∧
        recorded.event.event = event domain semantics ingress ∧
        recorded.nullifiers = [nullifier domain semantics ingress] then
      some (.ok (receipt domain semantics ingress))
    else some (.error ())

inductive Result where
  | confirmed (kind : DurableReceiverIO.Confirmation) (receipt : Receipt)
  | rejected (reason : Reject)
  | transactionConflict
  | durableRejected (reason : DurableDataIntent.RejectReason)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def receiveLoaded (deployment : Deployment) (semantics : Digest) (ambient : Ambient)
    (native : CredentialSignatureIO.NativeConfig) (transport : DurableReceiverIO.Transport)
    (durable : Durable) (bytes : List UInt8) : IO Result := do
  let some ingress := decodeIngress bytes
    | return .rejected .malformedIngress
  match replay deployment.domain semantics durable ingress with
  | some (.ok prior) => return .confirmed .replayed prior
  | some (.error _) => return .transactionConflict
  | none =>
    match ← admitDecodedNative deployment semantics ambient durable native ingress with
    | .error reason => return .rejected reason
    | .ok accepted =>
      match ← DurableReceiverIO.receiveLoaded transport rootBytes durable (intent accepted) with
      | .confirmed kind _ =>
          return .confirmed kind (receipt deployment.domain semantics ingress)
      | .rejected reason => return .durableRejected reason
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

#assert_axioms command_roundtrip
#assert_axioms commandCodec_injective
#assert_axioms AcceptedRefill.sound
#assert_axioms intent_install_refilled
#assert_axioms spent_empty
#assert_axioms notController_empty

end Minidregg.Kernel.MeterRefillReceiver
