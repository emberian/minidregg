/-
One signed fleet turn by an account holder. The turn always posts the pinned
base tariff from the paying account to the deployment collector in the one
canonical Book. It may also move value to another registered account, and it
may append one event to a topic stream owned by the paying account.

A topic stream is the existing typed append-only causal event log: one
`eventHistory` cell per stream (a StoreCodec cell, unbounded), not a side
channel. Its stream id, cell id, sequence position and parent event are
derived by this source from the paying account, the topic bytes and the
current cell; the event
record binds the exact payload digest, this turn's transaction id and effect
digest, the Book roots around the turn and the typed author. The payload bytes
themselves stay in the signed ingress retained by the accepted journal.

Authority is the ordinary account capability path: one native signature by
the current holder of a `transfer` capability over the paying account, checked
against that account's current installed law. Receiving value needs no
authority. The operation marker is the intent's durable nullifier (the Store's
consumed set; the authority cell is not written), so an exact repeat replays
and a changed command under the same identity conflicts.
-/
import Kernel.ParticipantKeyEnrollment
import Compiler.NativeHostCodec

namespace Minidregg.Kernel.FleetTurn

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.CredentialAuthorityEntryCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialAuthorityEffects
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.PolicyInstall
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.Store (Store Patch Op Address)
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev Snapshot := CredentialAuthorityDomain.Snapshot
abbrev AuthorityMaterializer := CredentialAuthorityCell.materializer
abbrev EventStore := Minidregg.Theory.Store.Store HyperdocumentEventLog.Sparse.layout

/-- One recorded topic event: its derived event key and its record. -/
structure EventEntry where
  key : Hyperdocument.VersionEventId
  record : Hyperdocument.VersionEventRecord

/-- Topic labels are bytes chosen by the account holder. They name a stream
of that account only; the same label under another account is another stream. -/
def maxTopicBytes : Nat := 64
/-- Payloads ride in the signed ingress; the topic cell stores only their digest. -/
def maxPayloadBytes : Nat := 16384

structure Transfer where
  destination : Nat
  asset : Nat
  amount : Nat
  deriving DecidableEq, Repr

structure Publication where
  topic : List UInt8
  sequence : Nat
  payload : List UInt8
  deriving DecidableEq, Repr

/-- `fee` is stated by the signer and must equal the pinned base tariff, so
the signature is a statement about the exact debit. -/
structure Command where
  subject : SubjectId
  payer : Nat
  spend : CapabilityId
  nonce : Nat
  fee : Nat
  transfer : Option Transfer
  publication : Option Publication
  deriving DecidableEq, Repr

def transferStream : StreamCodec Transfer :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat StreamCodec.nat))
    (fun t => (t.destination, t.asset, t.amount))
    (fun (destination, asset, amount) => ⟨destination, asset, amount⟩)
    (by intro t; cases t; rfl)

def publicationStream : StreamCodec Publication :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat bytesStream))
    (fun p => (p.topic, p.sequence, p.payload))
    (fun (topic, sequence, payload) => ⟨topic, sequence, payload⟩)
    (by intro p; cases p; rfl)

def commandStream : StreamCodec Command :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product capabilityIdStream
          (StreamCodec.product StreamCodec.nat
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.product (StreamCodec.option transferStream)
                (StreamCodec.option publicationStream)))))))
    (fun c => (c.subject, c.payer, c.spend, c.nonce, c.fee, c.transfer, c.publication))
    (fun (subject, payer, spend, nonce, fee, transfer, publication) =>
      ⟨subject, payer, spend, nonce, fee, transfer, publication⟩)
    (by intro c; cases c; rfl)

def commandFrame : List UInt8 := "DREGG/FLEET/TURN/v1".toUTF8.toList

def commandCodec : LawfulCodec Command :=
  NativeHostCodec.framed commandFrame commandStream

structure Ingress where
  commandBytes : List UInt8
  envelope : List UInt8
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap (StreamCodec.product bytesStream bytesStream)
    (fun ingress => (ingress.commandBytes, ingress.envelope))
    (fun (command, envelope) => ⟨command, envelope⟩)
    (by intro ingress; cases ingress; rfl)

def ingressCodec : LawfulCodec Ingress :=
  NativeHostCodec.framed "DREGG/FLEET/TURN/SIGNED/v1".toUTF8.toList ingressStream

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
    match envelopeExact :
        CredentialSignatureAdmission.canonicalEnvelopeCodec.decode ingress.envelope with
    | none => none
    | some envelope =>
      some ⟨ingress, command,
        NativeHostCodec.framed_canonical commandFrame commandStream commandExact,
        envelope, envelopeExact⟩

def DecodedIngress.bytes (ingress : DecodedIngress) : List UInt8 :=
  ingressCodec.encode ingress.ingress

def Command.transferAmount (command : Command) : Nat :=
  match command.transfer with
  | none => 0
  | some transfer => transfer.amount

/-- A turn must do something besides paying for itself; a transfer moves a
positive amount to another account; a topic event names a nonempty bounded
label, a positive sequence position and a bounded payload. -/
def Command.shapeOk (command : Command) : Bool :=
  (command.transfer.isSome || command.publication.isSome) &&
  (match command.transfer with
    | none => true
    | some transfer => decide (0 < transfer.amount) && transfer.destination != command.payer) &&
  (match command.publication with
    | none => true
    | some p => !p.topic.isEmpty && decide (p.topic.length ≤ maxTopicBytes) &&
        decide (p.payload.length ≤ maxPayloadBytes) && decide (0 < p.sequence))

private def cshake (customization : String) (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash customization.toUTF8.toList bytes).digest

/-- Operation identity: the signer, the paying account and the signer's nonce.
Every other command field is under the signature; a changed field with the same
identity is a conflict, never a second effect. -/
def marker (domain semantics : Digest) (command : Command) : Nat :=
  (cshake "DREGG.FLEET.TURN.IDENTITY/v1"
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
        (StreamCodec.product StreamCodec.nat StreamCodec.nat)))).encode
      (domain, semantics, command.subject, command.payer, command.nonce))).value

def streamDigest (domain : Digest) (payer : Nat) (topic : List UInt8) : Digest :=
  cshake "DREGG.FLEET.TOPIC.STREAM/v1"
    ((StreamCodec.product digestStream (StreamCodec.product StreamCodec.nat bytesStream)).encode
      (domain, payer, topic))

/-- The one event cell of a stream. -/
def topicCellId (stream : Digest) : Nat :=
  (cshake "DREGG.FLEET.TOPIC.CELL/v1" (digestStream.encode stream)).value

def payloadDigest (domain : Digest) (payload : List UInt8) : Digest :=
  cshake "DREGG.FLEET.TOPIC.PAYLOAD/v1"
    ((StreamCodec.product digestStream bytesStream).encode (domain, payload))

/-- The one schema of a fleet topic event record. -/
def eventSchema : CausalVersionDag.SchemaRef :=
  ⟨cshake "DREGG.FLEET.TOPIC.EVENT-SCHEMA/v1" [], 1⟩


structure Declaration where
  expectedPreRoot : Digest
  operationNullifier : Nat

def declarationStream : StreamCodec Declaration :=
  StreamCodec.xmap (StreamCodec.product digestStream StreamCodec.nat)
    (fun d => (d.expectedPreRoot, d.operationNullifier))
    (fun (root, nullifier) => ⟨root, nullifier⟩)
    (by intro d; cases d; rfl)

def declarationCodec : LawfulCodec Declaration :=
  ResourceBirthCodec.strictCodec declarationStream.toLawful

def declaration (snapshot : Snapshot) (semantics : Digest) (command : Command) : Declaration :=
  ⟨snapshot.cell.root, marker snapshot.domain semantics command⟩

/-- A fleet turn writes nothing in the authority cell: its only authority
effect is consuming the operation marker, and that is the intent's durable
nullifier (the Store's consumed set), not an authority-cell plane. The empty
patch is quoted at the pre-root, so the turn is still bound to the authority
state it was authorized against. -/
def Declaration.patch (_ : Declaration) : Patch CredentialAuthorityState.layout := []

structure Mode {M : Materializer} (pre : Cell M) (d : Declaration) : Type where
  rootExact : d.expectedPreRoot = pre.root

/-- The effect is determined by the exact command under the current law, so
its digest is computable from the retained ingress alone. The consumed marker
and pre-root are bound separately through the signed request. -/
def effectDigest (domain semantics : Digest) (command : Command) : Digest :=
  cshake "DREGG.FLEET.TURN.EFFECT/v1"
    ((StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream)).encode
      (domain, semantics, commandCodec.encode command))

structure Ambient where
  federation : FederationId
  height : Height

/-- The request is the ordinary account-spend request over the paying account,
under that account's own installed law. Its cost is everything the turn debits,
so a capability's `maxCost` bounds one turn's outflow. -/
def context (snapshot : Snapshot) (semantics : Digest) (ambient : Ambient)
    (command : Command) : RequestContext where
  authority :=
    { kind := .account
      domain := snapshot.domain
      semantics := semantics
      federation := ambient.federation
      subject := command.subject
      subjectKeyEpoch := snapshot.authState.subjectKeyEpoch command.subject
      target := ⟨command.payer⟩
      verb := .transfer
      nonce := marker snapshot.domain semantics command
      height := ambient.height
      policyId := ⟨command.payer⟩
      policyEpoch := snapshot.authState.policyEpoch ⟨command.payer⟩
      policyRevision := snapshot.authState.policyRevision ⟨command.payer⟩
      cost := command.fee + command.transferAmount }
  argsDigestBytes := fun bytes =>
    cshake "DREGG.FLEET.TURN.ARGS/v1" (commandCodec.encode command ++ bytes)

def request (snapshot : Snapshot) (semantics : Digest) (ambient : Ambient)
    (command : Command) : Request .account :=
  ((context snapshot semantics ambient command).request declarationCodec
    (fun _ => effectDigest snapshot.domain semantics command) snapshot.cell.root
    (marker snapshot.domain semantics command) (declaration snapshot semantics command)).2

def family (snapshot : Snapshot) (semantics : Digest) (ambient : Ambient) (command : Command) :
    SemanticEffectFamily CredentialAuthorityState.layout AuthorityMaterializer Nat where
  Declaration := Declaration
  declarationCodec := declarationCodec
  pre := snapshot.cell
  request := fun d => (context snapshot semantics ambient command).request
    declarationCodec (fun _ => effectDigest snapshot.domain semantics command) snapshot.cell.root
    d.operationNullifier d
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun d _ => Mode snapshot.cell d
  Postcondition := fun d _ post => d.patch.ResultAt snapshot.logical post
  effectDigest := fun _ => effectDigest snapshot.domain semantics command
  patch := fun d _ => d.patch
  nullifier := fun d _ => some d.operationNullifier
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

/-- The Book leg: the fee first, then the optional transfer, each reading the
Book left by the previous posting. -/
def batch (tariff : CreationTariff) (command : Command) : CanonicalResourceKernel.Batch where
  registrations := []
  operations := [.fee command.payer tariff.collector tariff.asset command.fee] ++
    match command.transfer with
    | none => []
    | some transfer => [.transfer command.payer transfer.destination transfer.asset transfer.amount]

inductive Reject where
  | malformedIngress | malformedCommand | feeMismatch
  | directoryUnavailable | authorityUnavailable | bookUnavailable | bookRefused
  | topicUnavailable | sequenceTaken | sequenceGap
  | replayedMarker | validation | physicalPreparation
  | policyUnavailable | capabilityRejected | policyRejected | policyInputRange | policyCastAlias
  | signature (reason : CredentialSignatureAdmission.Reject)
  deriving Repr

def requireSome {A : Type} (reason : Reject) : Option A → Except Reject A
  | none => .error reason
  | some value => .ok value

/-! ## Topic cells -/

/-- The events of one topic cell, in canonical store order. -/
def storedEvents (store : EventStore) : List EventEntry :=
  (StoreCodec.entries HyperdocumentCell.eventWire store).map fun entry => ⟨entry.1.2, entry.2⟩

/-- The recorded event at one stream position. -/
def eventAt (store : EventStore) (sequence : Nat) : Option EventEntry :=
  (storedEvents store).find? fun entry => entry.record.semanticVersion == sequence

def topicCell (store : EventStore) : PackedCell Registry :=
  ⟨.eventHistory, CellState.materialize HyperdocumentCell.eventMaterializer store⟩

/-- The current occupant of one derived topic cell id. A present cell of
another kind, or one that fails the event-history law, is not a topic. -/
inductive TopicRead where
  | fresh
  | live (cell : PackedCell Registry) (store : EventStore)

def readTopic (deployment : Deployment) (directory : Directory Nat Registry) (cellId : Nat) :
    Option TopicRead :=
  match directory.slots cellId with
  | .absent => some .fresh
  | .present _ =>
      match ResourceBirthController.Concrete.observeCell deployment directory cellId .eventHistory with
      | none => none
      | some observed => some (.live ⟨.eventHistory, observed.payload⟩ observed.payload.logical)

/-- The number of recorded events of a stream. Positions are admitted only in
order (`planTopic`), so a stream of `n` events holds exactly positions `1..n`. -/
def TopicRead.count : TopicRead → Nat
  | .fresh => 0
  | .live _ store => (storedEvents store).length

def TopicRead.store : TopicRead → EventStore
  | .fresh => 0
  | .live _ store => store

def TopicRead.image : TopicRead → LifecycleImage Registry
  | .fresh => .fresh
  | .live cell _ => .live cell

/-- Source-derived placement of one topic event: the stream's one cell, before
and after the append. -/
structure TopicPlan where
  stream : Digest
  cellId : Nat
  pre : LifecycleImage Registry
  post : EventStore
  entry : EventEntry

def TopicPlan.write (plan : TopicPlan) : DataWrite where
  cellId := ⟨plan.cellId⟩
  expectedPre := physicalRoot plan.pre
  exactPost := physicalRoot (.live (topicCell plan.post))
  canonicalPostBytes := LifecycleImage.bytes Registry (.live (topicCell plan.post))

def eventRecord (domain stream : Digest) (sequence : Nat) (payload : Digest)
    (parents : List Hyperdocument.VersionEventId) (bookPre bookPost txId effect : Digest)
    (author : Hyperdocument.PrincipalRef) : Hyperdocument.VersionEventRecord where
  historyDomain := domain
  document := ⟨stream⟩
  schema := eventSchema
  semanticVersion := sequence
  operation := ⟨payload⟩
  parents := parents
  preStateRoot := bookPre
  postStateRoot := bookPost
  requestId := txId
  effectId := effect
  author := author

def eventEntry (record : Hyperdocument.VersionEventRecord) : EventEntry :=
  ⟨Hyperdocument.deriveVersionEventId HyperdocumentCell.eventPreimageStream.toLawful
    HyperdocumentCell.eventDerivation record, record⟩

/-- Sequence `n` is admitted only as the stream's next position: the stream
holds exactly `n - 1` events and none at `n`. The parent is exactly the event
at `n - 1`; the first event has none. A live cell must be this stream's. -/
def planTopic (deployment : Deployment) (directory : Directory Nat Registry)
    (domain : Digest) (payer : Nat) (publication : Publication)
    (author : Hyperdocument.PrincipalRef) (bookPre bookPost txId effect : Digest) :
    Except Reject TopicPlan := do
  let stream := streamDigest domain payer publication.topic
  let cellId := topicCellId stream
  let current ← requireSome .topicUnavailable (readTopic deployment directory cellId)
  let store := current.store
  unless (storedEvents store).all (fun entry => entry.record.document == ⟨stream⟩) do
    throw .topicUnavailable
  if (eventAt store publication.sequence).isSome then throw .sequenceTaken
  if publication.sequence = 0 ∨ current.count + 1 ≠ publication.sequence then throw .sequenceGap
  let parents ← if publication.sequence = 1 then pure ([] : List Hyperdocument.VersionEventId)
    else match eventAt store (publication.sequence - 1) with
      | some previous => pure [previous.key]
      | none => throw .sequenceGap
  let record := eventRecord domain stream publication.sequence
    (payloadDigest domain publication.payload) parents bookPre bookPost txId effect author
  let entry := eventEntry record
  pure ⟨stream, cellId, current.image, store.update ⟨.events, entry.key⟩ (some record), entry⟩

/-! ## Preparation, authorization, plan -/

structure Prepared {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (tariff : CreationTariff)
    (ambient : Ambient) (durable : Durable) (command : Command) where
  private mk ::
  shape : command.shapeOk = true
  feeExact : command.fee = tariff.base
  directory : LoadedDirectory durable
  authority : Loaded deployment durable.snapshot
  book : ResourceBirthController.Concrete.ObservedCell deployment directory.directory
    deployment.resourceBookId .resourceBook
  resources : CanonicalResourceKernel.AcceptedBatch book.payload (batch tariff command)
  topic : Option TopicPlan
  candidate : Candidate (family authority.snapshot profile.semantics ambient command)
    authority.snapshot.cell (declaration authority.snapshot profile.semantics command) ()
  source : CanonicalCellRegistry.LoadedPolicySource authority.snapshot.domain directory.directory
    (authority.snapshot.authState.policyAddress ⟨command.payer⟩
      (authority.snapshot.authState.policyRevision ⟨command.payer⟩))

def prepare {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (tariff : CreationTariff) (ambient : Ambient)
    (durable : Durable) (command : Command) :
    Except Reject (Prepared deployment profile tariff ambient durable command) := do
  if shape : command.shapeOk = true then
    if feeExact : command.fee = tariff.base then
      let directory ← requireSome .directoryUnavailable (loadDirectory durable)
      let authority ← requireSome .authorityUnavailable (loadDeployment deployment durable.snapshot)
      let book ← requireSome .bookUnavailable
        (ResourceBirthController.Concrete.observeCell deployment directory.directory
          deployment.resourceBookId .resourceBook)
      let snapshot := authority.snapshot
      let d := declaration snapshot profile.semantics command
      if admission : (batch tariff command).Admission
          (CanonicalResourceKernel.logicalBook book.payload.logical) then
        let resources := CanonicalResourceKernel.AcceptedBatch.ofAdmission admission
        let topic ← match command.publication with
          | none => pure none
          | some publication =>
              (planTopic deployment directory.directory snapshot.domain
                command.payer publication ⟨command.subject, .account, command.spend⟩
                book.payload.root resources.post.root
                ⟨marker snapshot.domain profile.semantics command⟩
                (effectDigest snapshot.domain profile.semantics command)).map some
        if snapshot.spent d.operationNullifier = false then
          match validate AuthorityMaterializer snapshot.cell snapshot.cell.root d.patch with
          | .rejected _ => throw .validation
          | .accepted validated =>
              let source ← requireSome .policyUnavailable (CanonicalCellRegistry.loadPolicySource
                snapshot.domain directory.directory
                (snapshot.authState.policyAddress ⟨command.payer⟩
                  (snapshot.authState.policyRevision ⟨command.payer⟩)))
              let candidate : Candidate (family snapshot profile.semantics ambient command)
                  snapshot.cell d () :=
                { preStateBound := rfl
                  modeEvidence := ⟨rfl⟩
                  validated := validated
                  postcondition := validated.resultAt }
              pure ⟨shape, feeExact, directory, authority, book, resources, topic, candidate, source⟩
        else throw .replayedMarker
      else throw .bookRefused
    else throw .feeMismatch
  else throw .malformedCommand

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {tariff : CreationTariff} {ambient : Ambient}
  {durable : Durable} {command : Command}

def balanceSlot (label : String) (book : CanonicalResourceKernel.Book) (account asset : Nat) :
    String × Int :=
  (label, book.balance account asset)

/-- The installed account law sees the exact request, the stated debit and
destination, the paying account's fee-asset balance before and after the Book
leg, the complete command bytes and the presented spend grant. -/
def project (prepared : Prepared deployment profile tariff ambient durable command)
    (logical : Store CredentialAuthorityState.layout) : Minidregg.Pred.State :=
  let before := CanonicalResourceKernel.logicalBook prepared.book.payload.logical
  let after := CanonicalResourceKernel.logicalBook prepared.resources.post.logical
  let (destination, asset, amount) := match command.transfer with
    | none => (0, 0, 0)
    | some transfer => (transfer.destination, transfer.asset, transfer.amount)
  let sequence := match command.publication with
    | none => 0
    | some publication => publication.sequence
  ⟨CanonicalRuntimeProfile.requestSlots
      (request prepared.authority.snapshot profile.semantics ambient command) ++
    ([("fleet/operation/turn", 1), ("fleet/fee", (command.fee : Int)),
     ("fleet/transfer/destination", (destination : Int)), ("fleet/transfer/asset", (asset : Int)),
     ("fleet/transfer/amount", (amount : Int)),
     ("fleet/publication", if command.publication.isSome then 1 else 0),
     ("fleet/publication/sequence", (sequence : Int)),
     balanceSlot "fleet/payer/balance/before" before command.payer tariff.asset,
     balanceSlot "fleet/payer/balance/after" after command.payer tariff.asset] :
      List (String × Int)) ++
    ResourceAuthorityProjection.bytesSlots "command/bytes" 0 (commandCodec.encode command) ++
    ResourceAuthorityProjection.grantSlots "authority/spend" .account command.spend logical⟩

def step (prepared : Prepared deployment profile tariff ambient durable command) : PolicyStepContext :=
  PolicyStepContext.ofCandidate (project prepared) profile.semantics prepared.candidate

def sourceStore (prepared : Prepared deployment profile tariff ambient durable command) :
    CanonicalPolicyRegistry.PayloadStore :=
  ⟨CanonicalCellRegistry.fetchPolicySource prepared.authority.snapshot.domain
    prepared.directory.directory⟩

def policyConfig [DecidableEq F]
    (prepared : Prepared deployment profile tariff ambient durable command) : CanonicalPolicyConfig F :=
  CredentialAuthorityPolicyRegistry.config profile.compilerProfile prepared.authority.snapshot
    (sourceStore prepared)
    (sourceCapabilityPortal prepared.authority.snapshot
      (marker prepared.authority.snapshot.domain profile.semantics command))
    (step prepared)

abbrev Prepared.SemanticAccepted [DecidableEq F]
    (prepared : Prepared deployment profile tariff ambient durable command) :=
  AcceptedCellEffect (portal := (policyConfig prepared).portal)
    (authState := prepared.authority.snapshot.authState)
    (family prepared.authority.snapshot profile.semantics ambient command)
    (request prepared.authority.snapshot profile.semantics ambient command)
    prepared.authority.snapshot.cell
    (declaration prepared.authority.snapshot profile.semantics command) ()

def authorize [DecidableEq F]
    (prepared : Prepared deployment profile tariff ambient durable command)
    (receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot) :
    Except Reject prepared.SemanticAccepted := do
  let wanted := request prepared.authority.snapshot profile.semantics ambient command
  let config := policyConfig prepared
  let evidence ← requireSome .capabilityRejected
    (sourceCapabilityOnlyEvidence profile.compilerProfile prepared.authority.snapshot
      (sourceStore prepared)
      (marker prepared.authority.snapshot.domain profile.semantics command) (step prepared)
      wanted command.spend receipt)
  let committed ← requireSome .policyUnavailable
    (config.registry.resolve wanted.policyId wanted.policyRevision)
  let witness := canonicalWitness profile.compilerProfile.compiler committed
    (step prepared).oldState (step prepared).newState
  if inputsInRange profile.compilerProfile.compiler committed.record.predicate
      witness.oldState witness.newState != true then
    throw .policyInputRange
  if !decide (castInjOn F
      (intsOf committed.record.predicate witness.oldState witness.newState)) then
    throw .policyCastAlias
  match CanonicalPolicyAdmission.admit config prepared.authority.snapshot.authState wanted
      evidence witness (.policy wanted.policyId wanted.policyRevision) rfl rfl with
  | none => .error .policyRejected
  | some authorization =>
      .ok (prepared.candidate.accept authorization rfl rfl rfl .sealed trivial)

structure Accepted [DecidableEq F]
    (prepared : Prepared deployment profile tariff ambient durable command)
    (ingress : DecodedIngress) where
  private mk ::
  receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot
  envelopeExact : receipt.envelopeBytes = ingress.ingress.envelope
  semantic : prepared.SemanticAccepted

def admitNative [DecidableEq F] (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared deployment profile tariff ambient durable command)
    (ingress : DecodedIngress) : IO (Except Reject (Accepted prepared ingress)) := do
  match ← CredentialSignatureAdmission.verifyNative native prepared.authority.snapshot
      (marker prepared.authority.snapshot.domain profile.semantics command)
      (request prepared.authority.snapshot profile.semantics ambient command)
      ingress.ingress.envelope with
  | .error reason => return .error (.signature reason)
  | .ok receipt =>
      if same : receipt.envelopeBytes = ingress.ingress.envelope then
        match authorize prepared receipt with
        | .error reason => return .error reason
        | .ok semantic => return .ok ⟨receipt, same, semantic⟩
      else return .error .capabilityRejected

/-- The source finalizes the draft's fee and next topic position before any
signing; the holder signs the exact finalized header. -/
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
  NativeHostCodec.framed "DREGG/FLEET/TURN/PLAN/v1".toUTF8.toList signingPlanStream

/-! ## Topic reading -/

/-- The stream head: the highest occupied sequence, which is the number of
recorded events (positions are admitted only in order). -/
def streamHead (deployment : Deployment) (directory : Directory Nat Registry)
    (stream : Digest) : Nat :=
  match readTopic deployment directory (topicCellId stream) with
  | some current => current.count
  | none => 0

/-- Events of one stream with sequence strictly above `cursor`, in order, at
most `limit` of them. A gap ends the read. -/
def eventsSince (deployment : Deployment) (directory : Directory Nat Registry)
    (stream : Digest) (cursor limit : Nat) : List EventEntry :=
  match readTopic deployment directory (topicCellId stream) with
  | some (.live _ store) =>
      let rec collect : Nat → Nat → List EventEntry → List EventEntry
        | 0, _, acc => acc.reverse
        | fuel + 1, sequence, acc =>
            match eventAt store sequence with
            | some entry => collect fuel (sequence + 1) (entry :: acc)
            | none => acc.reverse
      collect limit (cursor + 1) []
  | _ => []

end Minidregg.Kernel.FleetTurn
