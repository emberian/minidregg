/-
# Kernel.SeatReceiver — seats and invitations as signed native commands

Every seat turn is one signed native command (`Command`: subject, nonce, the
pinned authority root, one `SeatStore.Turn`, and the capabilities that
authorize it), admitted the way every kernel family is admitted (the clock
tick, job money, certify, the kernel activity): the signer's Ed25519 signature
over the exact request header (`CredentialSignatureAdmission.verifyNative`, the
subject's current enrolled key), its single-use marker as the intent's durable
nullifier, the authority cell as a read guard, the durable receiving loop
(`DurableReceiverIO.receiveLoaded`: CAS on every write, claims, the tail bound),
and the replay walk (`NativeHostReplay`) re-admitting the retained ingress at
its original height on every reopen and audit.

The turn the kernel decides is its intent, under this receiver's seal:
`Prepared.intent` is literally `SeatStore.Decided.intent` with the sealing
`admissionSeal`, so every kernel theorem stated over a decided turn holds of
what this receiver commits (`native_turn_is_kernel_turn`,
`native_invariant_preserved`, `native_turn_conserves`).

**Who may.**
* `publish`: the payer the stored package names owns that Book account
  (`accountHolder`); `handOver`: the signature, the kernel judges the holder.
* `create` an instance on an object, and `invoke` its method: a holder of an
  admissible capability on the instance OBJECT (`objectHolder`: the authority
  layer's own `capabilityAdmissibleCheck`), paying the invocation's envelope from
  a Book account it owns (`accountHolder`). The holder chooses WHEN the method
  runs and with what input, never what it does: a reallocation or a mint is
  only ever a member of the Plan the instance's own package code returns when
  the receiver re-executes it (`reallocate_requires_instance_holder`); there is
  no signed `reallocate` or `mint` command. Offerers are protected by offer
  safety, exit and conservation, whoever invokes the method; the contract can
  propose only what its code computes.
* `offer`: the signer owns the funding account (`offer_requires_account_holder`),
  and when it names an activity as the seat's holder, it is that activity's
  payer and the activity is still awaiting (`notActivityPayer`). The seat's Book
  account is its protected coordinate; the offerer never names it.
* `exit`: the kernel's `exitAuthorized` (offerer on demand, anyone after the
  deadline); the instance's clause is never consulted
  (`exit_requires_offerer_or_deadline`).

**The signature binds the outcome.** The signed request's effect digest commits
to the command bytes and to the digest of the decided turn's posts
(`Declaration`), computed by the Host at planning: a method whose Plan, or a
reallocation whose result, changed between the signing plan and the submission
no longer matches the signed header and is refused, never settled differently.
(An offer tolerates movement in the price; the exact signed plan does not.)
-/
import Kernel.CapabilityRevocationController
import Kernel.ResourceBirthController
import Kernel.SeatStore
import Kernel.PayAssignmentReceiver

namespace Minidregg.Kernel.SeatReceiver

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.CredentialAuthorityEntryCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ObjectiveActivityWire
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialAuthorityEffects
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.ObjectiveActivity (Config)
open Minidregg.Kernel.ObjectiveKernelConfig (Ambient configOf)
open Minidregg.Kernel.SeatStore (Turn Request Decided decideTurn turnStream transactionOf)

set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev Snapshot := CredentialAuthorityDomain.Snapshot

/-! ## Command and ingress -/

/-- The capabilities a command presents: one on the object it acts on (an
instance's object), one on the Book account it spends. -/
structure Grants where
  object : Option CapabilityId
  account : Option CapabilityId
  deriving DecidableEq, Repr

def grantsStream : StreamCodec Grants :=
  StreamCodec.xmap (StreamCodec.product (StreamCodec.option capabilityIdStream) (StreamCodec.option capabilityIdStream))
    (fun g => (g.object, g.account)) (fun w => ⟨w.1, w.2⟩) (by intro g; cases g; rfl)

structure Command where
  subject : SubjectId
  nonce : Nat
  expectedAuthorityRoot : Digest
  turn : Turn
  grants : Grants
  deriving DecidableEq, Repr

def commandStream : StreamCodec Command :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product StreamCodec.nat (StreamCodec.product digestStream
        (StreamCodec.product turnStream grantsStream))))
    (fun c => (c.subject, c.nonce, c.expectedAuthorityRoot, c.turn, c.grants))
    (fun (subject, nonce, root, turn, grants) => ⟨subject, nonce, root, turn, grants⟩)
    (by intro c; cases c; rfl)

def commandFrame : List UInt8 := "DREGG/SEAT/COMMAND/v1".toUTF8.toList

def commandCodec : LawfulCodec Command := ObjectiveActivityWire.framed commandFrame commandStream

theorem command_roundtrip (command : Command) :
    commandCodec.decode (commandCodec.encode command) = some command :=
  commandCodec.decode_encode command

theorem command_canonical {bytes : List UInt8} {command : Command}
    (accepted : commandCodec.decode bytes = some command) : commandCodec.encode command = bytes :=
  ObjectiveActivityWire.framed_canonical accepted

def Command.request (command : Command) : Request := ⟨command.subject, command.nonce, command.turn⟩

structure Ingress where
  commandBytes : List UInt8
  envelope : List UInt8
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap (StreamCodec.product bytesStream bytesStream)
    (fun ingress => (ingress.commandBytes, ingress.envelope))
    (fun (command, envelope) => ⟨command, envelope⟩)
    (by intro ingress; cases ingress; rfl)

def ingressFrame : List UInt8 := "DREGG/SEAT/SIGNED/v1".toUTF8.toList

def ingressCodec : LawfulCodec Ingress := ObjectiveActivityWire.framed ingressFrame ingressStream

structure DecodedIngress where
  private mk ::
  ingress : Ingress
  command : Command
  canonical : commandCodec.encode command = ingress.commandBytes
  envelope : CredentialSignedEnvelopeController.SignedEnvelope
  envelopeExact : CredentialSignatureAdmission.canonicalEnvelopeCodec.decode ingress.envelope =
    some envelope

def decodeIngress (bytes : List UInt8) : Option DecodedIngress := do
  let ingress ← ingressCodec.decode bytes
  match commandExact : commandCodec.decode ingress.commandBytes with
  | none => none
  | some command =>
    match envelopeExact : CredentialSignatureAdmission.canonicalEnvelopeCodec.decode ingress.envelope with
    | none => none
    | some envelope => some ⟨ingress, command, command_canonical commandExact, envelope, envelopeExact⟩

def DecodedIngress.bytes (ingress : DecodedIngress) : List UInt8 :=
  ingressCodec.encode ingress.ingress

def marker (domain semantics : Digest) (command : Command) : Nat :=
  (Sp800185Cshake256.hash "DREGG.SEAT.IDENTITY/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream StreamCodec.nat))).encode
      (domain, semantics, command.subject, command.nonce))).digest.value

/-! ## Refusals -/

inductive Reject where
  | malformedIngress | directoryUnavailable | authorityUnavailable | staleAuthority
  | replayedMarker | physicalPreparation
  | config (reason : ObjectiveActivity.Refusal)
  | kernel (reason : SeatStore.Refusal)
  /-- The signer holds no capability admissible for mutating the object. -/
  | notObjectHolder
  /-- The signer does not own the Book account the turn spends. -/
  | notAccountOwner
  /-- The named holder activity is not an awaiting activity this signer pays for. -/
  | notActivityPayer
  | signature (reason : CredentialSignatureAdmission.Reject)
  deriving Repr

/-! ## The decided outcome and the signed request -/

def postStream : StreamCodec Post :=
  StreamCodec.xmap (StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream))
    (fun post => (post.cell, post.pre, post.bytes)) (fun (cell, pre, bytes) => ⟨cell, pre, bytes⟩)
    (by intro post; cases post; rfl)

/-- The outcome a signer consents to: the decided turn's posts. -/
def outcomeDigest (posts : List Post) : Digest :=
  (Sp800185Cshake256.hash "DREGG.SEAT.OUTCOME/v1".toUTF8.toList
    ((StreamCodec.list postStream).encode posts)).digest

/-- What the signature covers besides the command: the decided outcome, and
the marker. -/
structure Declaration where
  outcome : Digest
  operationNullifier : Nat

def declarationStream : StreamCodec Declaration :=
  StreamCodec.xmap (StreamCodec.product digestStream StreamCodec.nat)
    (fun d => (d.outcome, d.operationNullifier)) (fun (outcome, nullifier) => ⟨outcome, nullifier⟩)
    (by intro d; cases d; rfl)

def declarationCodec : LawfulCodec Declaration :=
  ResourceBirthCodec.strictCodec declarationStream.toLawful

def effectDigest (domain semantics : Digest) (command : Command) (d : Declaration) : Digest :=
  (Sp800185Cshake256.hash "DREGG.SEAT.EFFECT/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product bytesStream bytesStream))).encode
      (domain, semantics, commandCodec.encode command, declarationCodec.encode d))).digest

/-- The resource a command's signed request targets: the instance object for a
creation or an invocation, the funding account for an offer, and the turn's
own seat cell otherwise. -/
def signedTarget (domain : Digest) (command : Command) : ResourceKind × Nat :=
  match command.turn with
  | .publish stored => (.object, (SeatStore.packageCell domain (SeatStore.publishedPin stored)).value)
  | .create inst _ _ => (.object, inst)
  | .handOver invitation _ => (.object, (SeatStore.invitationCell domain invitation).value)
  | .offer _ _ funding _ _ _ => (.account, funding)
  | .invoke inst _ _ _ => (.object, inst)
  | .exit seat => (.object, seat)

def verbFor : (kind : ResourceKind) → Verb kind
  | .object => .mutateObject
  | .account => .transfer
  | .program => .installProgram

def contextAt (snapshot : Snapshot) (semantics : Digest) (ambient : Ambient) (command : Command)
    (kind : ResourceKind) (target : Nat) : RequestContext where
  authority :=
    { kind := kind
      domain := snapshot.domain
      semantics := semantics
      federation := ambient.federation
      subject := command.subject
      subjectKeyEpoch := snapshot.authState.subjectKeyEpoch command.subject
      target := ⟨target⟩
      verb := verbFor kind
      nonce := marker snapshot.domain semantics command
      height := ambient.height
      policyId := ⟨target⟩
      policyEpoch := snapshot.authState.policyEpoch ⟨target⟩
      policyRevision := snapshot.authState.policyRevision ⟨target⟩
      cost := (commandCodec.encode command).length }
  argsDigestBytes := fun bytes =>
    (Sp800185Cshake256.hash "DREGG.SEAT.ARGS/v1".toUTF8.toList
      (commandCodec.encode command ++ bytes)).digest

def requestAt (snapshot : Snapshot) (semantics : Digest) (ambient : Ambient) (command : Command)
    (kind : ResourceKind) (target : Nat) (preRoot : Digest) (outcome : Digest) : PackedEffectRequest :=
  (contextAt snapshot semantics ambient command kind target).request declarationCodec
    (effectDigest snapshot.domain semantics command) preRoot
    (marker snapshot.domain semantics command) ⟨outcome, marker snapshot.domain semantics command⟩

def signedRequest (snapshot : Snapshot) (semantics : Digest) (ambient : Ambient) (command : Command)
    (preRoot : Digest) (outcome : Digest) : PackedEffectRequest :=
  let (kind, target) := signedTarget snapshot.domain command
  requestAt snapshot semantics ambient command kind target preRoot outcome

/-! ## Who may: object holders, account owners, activity payers -/

def objectHolder (snapshot : Snapshot) (semantics : Digest) (ambient : Ambient) (command : Command)
    (object : Nat) (capability : Option CapabilityId) (preRoot outcome : Digest) : Bool :=
  match capability with
  | none => false
  | some capability =>
    match readCapability snapshot.cell .object capability with
    | none => false
    | some stored =>
        match requestAt snapshot semantics ambient command .object object preRoot outcome with
        | ⟨.object, request⟩ => AuthorizationDeclaration.capabilityAdmissibleCheck stored.head snapshot.authState request
        | _ => false

def accountHolder (snapshot : Snapshot) (semantics : Digest) (ambient : Ambient) (command : Command)
    (account : Nat) (capability : Option CapabilityId) (preRoot outcome : Digest) : Bool :=
  match capability with
  | none => false
  | some capability =>
    let stored := readCapability snapshot.cell .account capability
    decide (PayAssignmentReceiver.OwnerGrant stored command.subject account) &&
      match stored with
      | none => false
      | some stored =>
          match requestAt snapshot semantics ambient command .account account preRoot outcome with
          | ⟨.account, request⟩ => AuthorizationDeclaration.capabilityAdmissibleCheck stored.head snapshot.authState request
          | _ => false

/-- The signer pays for the awaiting activity at `record` (its escrow's payer):
only it may make the activity a seat's holder, whose end exits the seat. -/
def activityPayer {rootBytes : List UInt8 → Digest} (snapshot : DataSnapshot rootBytes) (subject : SubjectId)
    (record : Nat) : Bool :=
  match ObjectiveActivity.readRecord snapshot ⟨record⟩ with
  | some found => found.escrow.payer == subject && match found.phase with
      | .awaiting _ => true
      | _ => false
  | none => false

/-- The authority a command needs beyond its signature. -/
def authorized {rootBytes : List UInt8 → Digest} (data : DataSnapshot rootBytes) (snapshot : Snapshot)
    (semantics : Digest) (ambient : Ambient) (command : Command) (preRoot outcome : Digest) : Except Reject Unit :=
  let object (o : Nat) : Except Reject Unit :=
    if objectHolder snapshot semantics ambient command o command.grants.object preRoot outcome then .ok ()
    else .error .notObjectHolder
  let account (a : Nat) : Except Reject Unit :=
    if accountHolder snapshot semantics ambient command a command.grants.account preRoot outcome then .ok ()
    else .error .notAccountOwner
  match command.turn with
  | .handOver _ _ | .exit _ => .ok ()
  -- the publication's payer (named in the stored bytes) consents by its account grant
  | .publish stored => account ((ObjectiveActivity.decodeStored stored).map (·.payer) |>.getD 0)
  | .create inst _ _ => object inst
  | .invoke inst _ _ payer => do object inst; account payer
  | .offer _ _ funding _ _ holder => do
      account funding
      match holder with
      | none => pure ()
      | some record => if activityPayer data command.subject record then pure () else throw .notActivityPayer

/-! ## Preparation -/

def requireSome {A : Type} (reason : Reject) : Option A → Except Reject A
  | none => .error reason
  | some value => .ok value

structure Prepared {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (command : Command) where
  private mk ::
  directory : LoadedDirectory durable
  authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot
  config : Config
  configExact : configOf deployment profile ambient = .ok config
  decided : Decided config durable.snapshot ambient.height command.request
  decidedExact : decideTurn config durable.snapshot ambient.height command.request = .ok decided
  preRoot : Digest
  preRootExact : preRoot = durable.snapshot.model.roots ⟨(signedTarget deployment.domain command).2⟩
  outcome : Digest
  outcomeExact : outcome = outcomeDigest decided.posts
  authorizedExact : authorized durable.snapshot authority.snapshot profile.semantics ambient command preRoot outcome = .ok ()

def prepare {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (command : Command) : Except Reject (Prepared deployment profile ambient durable command) := do
  let directory ← requireSome .directoryUnavailable (loadDirectory durable)
  let authority ← requireSome .authorityUnavailable (loadDeployment deployment durable.snapshot)
  let snapshot := authority.snapshot
  if command.expectedAuthorityRoot ≠ snapshot.cell.root then throw .staleAuthority
  if snapshot.spent (marker snapshot.domain profile.semantics command) then throw .replayedMarker
  match configExact : configOf deployment profile ambient with
  | .error reason => throw (.config reason)
  | .ok config =>
    match decidedExact : decideTurn config durable.snapshot ambient.height command.request with
    | .error reason => throw (.kernel reason)
    | .ok decided =>
      let preRoot := durable.snapshot.model.roots ⟨(signedTarget deployment.domain command).2⟩
      let outcome := outcomeDigest decided.posts
      match authorizedExact : authorized durable.snapshot snapshot profile.semantics ambient command preRoot outcome with
      | .error reason => throw reason
      | .ok () =>
        pure ⟨directory, authority, config, configExact, decided, decidedExact, preRoot, rfl, outcome, rfl,
          authorizedExact⟩

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {command : Command}

def Prepared.request (prepared : Prepared deployment profile ambient durable command) : PackedEffectRequest :=
  signedRequest prepared.authority.snapshot profile.semantics ambient command prepared.preRoot prepared.outcome

/-! ## The receiver -/

def transactionId (_domain _semantics : Digest) (ingress : DecodedIngress) : Digest :=
  transactionOf ingress.command.request

def event (domain _semantics : Digest) (ingress : DecodedIngress) : StableEvent where
  codecVersion := 1
  domain := domain
  eventId := (Sp800185Cshake256.hash "DREGG.SEAT.EVENT/v1".toUTF8.toList ingress.bytes).digest
  canonicalBytes := ingress.bytes

def nullifier (domain semantics : Digest) (command : Command) : StableNullifier :=
  CredentialAuthorityReplay.nullifier domain (marker domain semantics command)

/-- The exact charge of a turn's footprint. -/
def charge (ingress : DecodedIngress) (posts : List Post) (guards : List ReadGuard) : ResourceCost.Charge
  | .incidences => 1
  | .turnBytes => ingress.bytes.length
  | .memoryTouches => posts.length + guards.length
  | .storageBytes => (posts.map fun post => post.bytes.length).sum
  | .witnessBytes => ingress.ingress.envelope.length
  | .proofWork => 2
  | .feeDebit | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

/-- This receiver's sealing on the kernel turn: the authority guard, the signed
marker, the replay event carrying the signed ingress, the signer. -/
def admissionSeal (prepared : Prepared deployment profile ambient durable command) (ingress : DecodedIngress) : Seal :=
  ⟨prepared.authority.readGuards, [nullifier deployment.domain profile.semantics command],
    event deployment.domain profile.semantics ingress, some command.subject, charge ingress⟩

def Prepared.intent (prepared : Prepared deployment profile ambient durable command) (ingress : DecodedIngress) :
    DataIntent rootBytes :=
  prepared.decided.intent (admissionSeal prepared ingress)

/-- A cell a seat intent writes is a seat-kind cell at its coordinate, the Book, or a
cell the kernel retires: the registry's retired image at a protected coordinate (a
closed seat, `Kernel.SeatStore.statePosts`). -/
def SeatOrBook (deployment : Deployment) (write : DataWrite) : Prop :=
  write.cellId = ⟨deployment.resourceBookId⟩ ∨
    (∃ payload, SeatStore.payloadOf write.canonicalPostBytes = some payload ∧
      write.cellId.value = SeatCell.coordinate deployment.domain payload.role payload.key) ∨
    (write.canonicalPostBytes = ObjectiveActivity.retiredImage ∧ SeatCell.reservedBase ≤ write.cellId.value)

instance (deployment : Deployment) (write : DataWrite) : Decidable (SeatOrBook deployment write) :=
  if book : write.cellId = ⟨deployment.resourceBookId⟩ then isTrue (Or.inl book)
  else if retired : write.canonicalPostBytes = ObjectiveActivity.retiredImage ∧
      SeatCell.reservedBase ≤ write.cellId.value then isTrue (Or.inr (Or.inr retired))
  else match found : SeatStore.payloadOf write.canonicalPostBytes with
    | none => isFalse (by
        rintro (h | ⟨payload, hp, _⟩ | h)
        · exact book h
        · rw [found] at hp; cases hp
        · exact retired h)
    | some payload =>
      if at_ : write.cellId.value = SeatCell.coordinate deployment.domain payload.role payload.key then
        isTrue (Or.inr (Or.inl ⟨payload, found, at_⟩))
      else isFalse (by
        rintro (h | ⟨other, hp, hat⟩ | h)
        · exact book h
        · rw [found] at hp; cases hp; exact at_ hat
        · exact retired h)

def PhysicalShape (prepared : Prepared deployment profile ambient durable command) (ingress : DecodedIngress) :
    Prop :=
  let intent := prepared.intent ingress
  (intent.writes.map DataWrite.cellId).Nodup ∧
    (∀ write ∈ intent.writes, write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
    (∀ write ∈ intent.writes, ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
    (∀ write ∈ intent.writes, SeatOrBook deployment write) ∧
    (∀ guard ∈ intent.readGuards, guard.expectedRoot = durable.snapshot.model.roots guard.cellId)

instance physicalShapeDecidable (prepared : Prepared deployment profile ambient durable command)
    (ingress : DecodedIngress) : Decidable (PhysicalShape prepared ingress) := by
  unfold PhysicalShape
  infer_instance

structure Accepted [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (ingress : DecodedIngress) where
  private mk ::
  prepared : Prepared deployment profile ambient durable ingress.command
  receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot
  envelopeExact : receipt.envelopeBytes = ingress.ingress.envelope
  physical : PhysicalShape prepared ingress

def admitDecodedNative [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (native : CredentialSignatureIO.NativeConfig) (ingress : DecodedIngress) :
    IO (Except Reject (Accepted deployment profile ambient durable ingress)) := do
  match prepare deployment profile ambient durable ingress.command with
  | .error reason => return .error reason
  | .ok prepared =>
    if physical : PhysicalShape prepared ingress then
      let ⟨kind, request⟩ := prepared.request
      match ← CredentialSignatureAdmission.verifyNative native prepared.authority.snapshot
          (marker prepared.authority.snapshot.domain profile.semantics ingress.command)
          request ingress.ingress.envelope with
      | .error reason => return .error (.signature reason)
      | .ok receipt =>
          if same : receipt.envelopeBytes = ingress.ingress.envelope then
            return .ok ⟨prepared, receipt, same, physical⟩
          else return .error (.signature (.envelope .invalidSignature))
    else return .error .physicalPreparation

variable [DecidableEq F] {ingress : DecodedIngress}

def intent (accepted : Accepted deployment profile ambient durable ingress) : DataIntent rootBytes :=
  accepted.prepared.intent ingress

/-! ## What an accepted turn is -/

/-- **The native turn is the kernel turn.** An accepted command commits exactly
the decided turn's intent under this receiver's seal: the kernel's own run on
the cells it loaded, its posts and its one batch. -/
theorem native_turn_is_kernel_turn (accepted : Accepted deployment profile ambient durable ingress) :
    intent accepted = accepted.prepared.decided.intent (admissionSeal accepted.prepared ingress) := rfl

/-- **T3 (a) holds of what the Host commits.** If every open seat the turn
loaded satisfied the seat invariant, every seat it writes does. -/
theorem native_invariant_preserved (accepted : Accepted deployment profile ambient durable ingress)
    (inv : Seats.Inv accepted.prepared.decided.world) : Seats.Inv accepted.prepared.decided.next :=
  accepted.prepared.decided.inv inv

/-- **T3 (c) holds of what the Host commits**: the Book it writes conserves
every asset. -/
theorem native_turn_conserves (accepted : Accepted deployment profile ambient durable ingress)
    (asset : Theory.CanonicalResourceKernel.AssetId) :
    (Theory.CanonicalResourceKernel.logicalBook accepted.prepared.decided.accepted.post.logical).totalAsset asset =
      (Theory.CanonicalResourceKernel.logicalBook accepted.prepared.decided.book.logical).totalAsset asset :=
  accepted.prepared.decided.conserves asset

/-- **Protected coordinates.** Every cell an accepted seat turn writes is a seat
cell at its own coordinate, or the deployment's Book. -/
theorem intent_writes_seat_or_book (accepted : Accepted deployment profile ambient durable ingress) :
    ∀ write ∈ (intent accepted).writes, SeatOrBook deployment write :=
  accepted.physical.2.2.2.1

/-- Every write of an accepted turn satisfies the registry's loaded-and-final law. -/
theorem intent_writes_lawful (accepted : Accepted deployment profile ambient durable ingress) :
    ∀ write ∈ (intent accepted).writes, ResourceBirthController.Concrete.PhysicalPostLaw deployment write :=
  accepted.physical.2.2.1

/-- **Only the funding account's owner offers.** -/
theorem offer_requires_account_holder (accepted : Accepted deployment profile ambient durable ingress)
    {invitation : Invitations.InvitationId} {expect : Invitations.Expectation} {funding payee : Nat}
    {proposal : Seats.Proposal} {holder : Option Nat}
    (turn : ingress.command.turn = .offer invitation expect funding payee proposal holder) :
    accountHolder accepted.prepared.authority.snapshot profile.semantics ambient ingress.command funding
      ingress.command.grants.account accepted.prepared.preRoot accepted.prepared.outcome = true := by
  have ok := accepted.prepared.authorizedExact
  unfold authorized at ok
  rw [turn] at ok
  by_cases owned : accountHolder accepted.prepared.authority.snapshot profile.semantics ambient ingress.command
      funding ingress.command.grants.account accepted.prepared.preRoot accepted.prepared.outcome = true
  · exact owned
  · simp [owned, bind, Except.bind] at ok

/-- **Only an instance holder runs the contract's method, and it pays.** A
reallocation or a mint exists only as a member of the Plan an `invoke`
re-executes; an accepted `invoke`'s signer holds a capability admissible for
mutating the instance object and owns the paying account. -/
theorem reallocate_requires_instance_holder (accepted : Accepted deployment profile ambient durable ingress)
    {inst payer : Nat} {input : List UInt8} {envelope : ObjectiveInvocationClaim.Capacity}
    (turn : ingress.command.turn = .invoke inst input envelope payer) :
    objectHolder accepted.prepared.authority.snapshot profile.semantics ambient ingress.command inst
        ingress.command.grants.object accepted.prepared.preRoot accepted.prepared.outcome = true ∧
      accountHolder accepted.prepared.authority.snapshot profile.semantics ambient ingress.command payer
        ingress.command.grants.account accepted.prepared.preRoot accepted.prepared.outcome = true := by
  have ok := accepted.prepared.authorizedExact
  unfold authorized at ok
  rw [turn] at ok
  by_cases held : objectHolder accepted.prepared.authority.snapshot profile.semantics ambient ingress.command
      inst ingress.command.grants.object accepted.prepared.preRoot accepted.prepared.outcome = true
  · by_cases owned : accountHolder accepted.prepared.authority.snapshot profile.semantics ambient
        ingress.command payer ingress.command.grants.account accepted.prepared.preRoot accepted.prepared.outcome = true
    · exact ⟨held, owned⟩
    · simp [held, owned, bind, Except.bind] at ok
  · simp [held, bind, Except.bind] at ok

/-- **Who may exit, natively.** An accepted exit closed an open seat its signer
may exit by the kernel's own rule (its offerer on demand, anyone at or after its
due height); the instance's clause is not consulted. -/
theorem exit_requires_offerer_or_deadline (accepted : Accepted deployment profile ambient durable ingress)
    {seat : Nat} (turn : ingress.command.turn = .exit seat) :
    ∃ found ∈ accepted.prepared.decided.world.seats, found.account = seat ∧
      Seats.exitAuthorized ambient.height (.subject ingress.command.subject) found = true :=
  Seats.exit_step_authorized (accepted.prepared.decided.stepExact _ _ (by
    simp [Command.request, turn, SeatStore.Turn.kernelAction]))

/-- **An invitation is spent once.** An accepted offer consumes its invitation's
durable claim: once it commits, no intent carrying that claim (another offer of
the same invitation, under any seal) is ever accepted, and its exact retry replays. -/
theorem native_offer_spends_invitation_once (accepted : Accepted deployment profile ambient durable ingress)
    {invitation : Invitations.InvitationId} {expect : Invitations.Expectation} {funding payee : Nat}
    {proposal : Seats.Proposal} {holder : Option Nat}
    (turn : ingress.command.turn = .offer invitation expect funding payee proposal holder)
    {next : DataSnapshot rootBytes}
    (installed : DurableDataIntent.execute .complete durable.snapshot (intent accepted) = .accepted next) :
    (∀ (later : DataIntent rootBytes), SeatStore.invitationClaim invitation ∈ later.nullifiers →
      ∀ schedule after, DurableDataIntent.execute schedule next later ≠ .accepted after) ∧
    (∀ schedule, DurableDataIntent.execute schedule next (intent accepted) = .replayed (intent accepted).erase) := by
  have carries : SeatStore.invitationClaim invitation ∈ (intent accepted).nullifiers := by
    show SeatStore.invitationClaim invitation ∈
      (intentOf rootBytes _ _ _ accepted.prepared.decided.nullifiers _).nullifiers
    rw [intentOf_nullifiers, accepted.prepared.decided.nullifiersExact]
    simp [Command.request, turn, SeatStore.Turn.claims]
  exact ⟨fun later again schedule after =>
      ObjectiveActivity.spent_claim_never_accepted carries installed later again schedule after,
    ObjectiveActivity.installed_retry_replays installed⟩

structure Receipt where
  transactionId : Digest
  eventId : Digest
  deriving DecidableEq, Repr

def receipt (domain semantics : Digest) (ingress : DecodedIngress) : Receipt :=
  ⟨transactionId domain semantics ingress, (event domain semantics ingress).eventId⟩

/-- A retained ingress finds its record by its transaction id: the exact
ingress replays, any other ingress under the same id is a conflict. -/
def replay (domain semantics : Digest) (durable : Durable) (ingress : DecodedIngress) :
    Option (Except Unit Receipt) :=
  match DurableCommitProtocol.Snapshot.lookupRecorded
      (transactionId domain semantics ingress) durable.snapshot.model.journal with
  | none => none
  | some recorded =>
    if recorded.transactionId = transactionId domain semantics ingress ∧
        recorded.event.event = event domain semantics ingress then
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

def receiveLoaded (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (durable : Durable)
    (bytes : List UInt8) : IO Result := do
  let some ingress := decodeIngress bytes
    | return .rejected .malformedIngress
  match replay deployment.domain profile.semantics durable ingress with
  | some (.ok prior) => return .confirmed .replayed prior
  | some (.error _) => return .transactionConflict
  | none =>
    match ← admitDecodedNative deployment profile ambient durable native ingress with
    | .error reason => return .rejected reason
    | .ok accepted =>
      match ← DurableReceiverIO.receiveLoaded transport rootBytes durable (intent accepted) with
      | .confirmed kind _ => return .confirmed kind (receipt deployment.domain profile.semantics ingress)
      | .rejected reason => return .durableRejected reason
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

/-! ## Signing plan -/

/-- The exact header the signer signs. When the kernel refuses the command, the
header is built over the empty outcome and the submission is refused with the
named reason. -/
def signingHeader (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) :
    Except String CredentialSignedEnvelopeController.SignedHeader := do
  let some authority := loadDeployment deployment durable.snapshot
    | .error "authority unavailable"
  let outcome := match configOf deployment profile ambient with
    | .ok config => match decideTurn config durable.snapshot ambient.height command.request with
      | .ok decided => outcomeDigest decided.posts
      | .error _ => outcomeDigest []
    | .error _ => outcomeDigest []
  let preRoot := durable.snapshot.model.roots ⟨(signedTarget deployment.domain command).2⟩
  (CredentialSignatureAdmission.signingHeader authority.snapshot
    (marker deployment.domain profile.semantics command)
    (signedRequest authority.snapshot profile.semantics ambient command preRoot outcome)).mapError
      (fun reason => s!"seat signer key: {repr reason}")

/-- What the planner says the kernel would do: the decision, or its refusal. -/
def planVerdict (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) : String :=
  match configOf deployment profile ambient with
  | .error reason => s!"refused: {repr reason}"
  | .ok config => match decideTurn config durable.snapshot ambient.height command.request with
    | .ok decided => s!"decided: {decided.posts.length} posts"
    | .error reason => s!"refused: {repr reason}"

structure SigningPlan where
  domain : Digest
  semantics : Digest
  commandBytes : List UInt8
  header : List UInt8
  deriving DecidableEq, Repr

def signingPlanStream : StreamCodec SigningPlan :=
  StreamCodec.xmap (StreamCodec.product digestStream
    (StreamCodec.product digestStream (StreamCodec.product bytesStream bytesStream)))
    (fun plan => (plan.domain, plan.semantics, plan.commandBytes, plan.header))
    (fun (domain, semantics, command, header) => ⟨domain, semantics, command, header⟩)
    (by intro plan; cases plan; rfl)

def signingPlanCodec : LawfulCodec SigningPlan :=
  ObjectiveActivityWire.framed "DREGG/SEAT/PLAN/v1".toUTF8.toList signingPlanStream

#assert_axioms command_roundtrip command_canonical native_turn_is_kernel_turn native_invariant_preserved
  native_turn_conserves intent_writes_seat_or_book intent_writes_lawful offer_requires_account_holder
  reallocate_requires_instance_holder exit_requires_offerer_or_deadline native_offer_spends_invitation_once

end Minidregg.Kernel.SeatReceiver
