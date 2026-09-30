/-
One signed fleet turn by an account holder. The turn always posts the pinned
base tariff from the paying account to the deployment collector in the one
canonical Book. It may also move value to another registered account, and it
may append one event to a topic stream owned by the paying account.

A topic stream is the existing typed append-only causal event log
(`eventHistory` pages, four slots each), not a side channel. Its stream id,
page cell ids, sequence position and parent event are derived by this source
from the paying account, the topic bytes and the current pages; the event
record binds the exact payload digest, this turn's transaction id and effect
digest, the Book roots around the turn and the typed author. The payload bytes
themselves stay in the signed ingress retained by the accepted journal.

Authority is the ordinary account capability path: one native signature by
the current holder of a `transfer` capability over the paying account, checked
against that account's current installed law. Receiving value needs no
authority. The operation marker is consumed in the authority cell, so an exact
repeat replays and a changed command under the same identity conflicts.
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
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev Snapshot := CredentialAuthorityDomain.Snapshot
abbrev AuthorityMaterializer := CredentialAuthorityStateCodec.materializer
abbrev EventPage := HyperdocumentEventPageMaterializer.Page
abbrev EventEntry := HyperdocumentEventPageMaterializer.Entry

/-- Topic labels are bytes chosen by the account holder. They name a stream
of that account only; the same label under another account is another stream. -/
def maxTopicBytes : Nat := 64
/-- Payloads ride in the signed ingress; the page stores only their digest. -/
def maxPayloadBytes : Nat := 16384
def pageCapacity : Nat := 4

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

def pageCellId (stream : Digest) (page : Nat) : Nat :=
  (cshake "DREGG.FLEET.TOPIC.PAGE/v1"
    ((StreamCodec.product digestStream StreamCodec.nat).encode (stream, page))).value

def payloadDigest (domain : Digest) (payload : List UInt8) : Digest :=
  cshake "DREGG.FLEET.TOPIC.PAYLOAD/v1"
    ((StreamCodec.product digestStream bytesStream).encode (domain, payload))

/-- The one schema of a fleet topic event record. -/
def eventSchema : CausalVersionDag.SchemaRef :=
  ⟨cshake "DREGG.FLEET.TOPIC.EVENT-SCHEMA/v1" [], 1⟩

def pageOf (sequence : Nat) : Nat := (sequence - 1) / pageCapacity
def slotOf (sequence : Nat) : Nat := (sequence - 1) % pageCapacity

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

def Declaration.patch (d : Declaration) : Patch CredentialAuthorityState.schema Digest where
  expectedPreRoot := d.expectedPreRoot
  fieldFootprint := {.nullifier d.operationNullifier}
  resourceFootprint := ∅
  fieldWrites := [⟨.nullifier d.operationNullifier, some true⟩]
  resourceWrites := []

structure Mode {M : Materializer} (pre : Cell M) (d : Declaration) : Type where
  rootExact : d.expectedPreRoot = pre.root
  fresh : isNullified pre d.operationNullifier = false

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
    SemanticEffectFamily CredentialAuthorityState.schema AuthorityMaterializer Nat where
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

def edits (snapshot : Snapshot) (d : Declaration) : List CredentialAuthorityDomain.Edit :=
  [CredentialAuthorityDomain.nullifierEdit snapshot d.operationNullifier]

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
  | topicPageUnavailable | sequenceTaken | sequenceGap
  | replayedMarker | authorityPreparation | validation | refinement | physicalPreparation
  | policyUnavailable | capabilityRejected | policyRejected | policyInputRange | policyCastAlias
  | signature (reason : CredentialSignatureAdmission.Reject)
  deriving Repr

def requireSome {A : Type} (reason : Reject) : Option A → Except Reject A
  | none => .error reason
  | some value => .ok value

/-! ## Topic pages -/

def slotAt (page : EventPage) : Nat → Option EventEntry
  | 0 => page.slot0
  | 1 => page.slot1
  | 2 => page.slot2
  | 3 => page.slot3
  | _ => none

def withSlot (page : EventPage) (slot : Nat) (entry : EventEntry) : EventPage :=
  match slot with
  | 0 => { page with slot0 := some entry }
  | 1 => { page with slot1 := some entry }
  | 2 => { page with slot2 := some entry }
  | _ => { page with slot3 := some entry }

def filledBelow (page : EventPage) (slot : Nat) : Bool :=
  (List.range slot).all fun index => (slotAt page index).isSome

def emptyPage (domain stream : Digest) (pageNumber : Nat) : EventPage :=
  ⟨domain, ⟨stream⟩, pageNumber, none, none, none, none⟩

def pageCell (page : EventPage) : PackedCell Registry :=
  ⟨.eventHistory, CellState.materialize HyperdocumentEventPageMaterializer.materializer
    (HyperdocumentEventPageMaterializer.stateOfOption (some page))⟩

/-- The current occupant of one derived page id. A present cell of another kind
or an empty event cell is not a topic page. -/
inductive PageRead where
  | fresh
  | live (cell : PackedCell Registry) (page : EventPage)

def readPage (deployment : Deployment) (directory : Directory Nat Registry) (cellId : Nat) :
    Option PageRead :=
  match directory.slots cellId with
  | .absent => some .fresh
  | .present _ =>
      match ResourceBirthController.Concrete.observeCell deployment directory cellId .eventHistory with
      | none => none
      | some observed =>
          match HyperdocumentEventPageMaterializer.pageAt observed.payload.logical with
          | none => none
          | some page => some (.live ⟨.eventHistory, observed.payload⟩ page)

def PageRead.image : PageRead → LifecycleImage Registry
  | .fresh => .fresh
  | .live cell _ => .live cell

/-- Source-derived placement of one topic event. `guards` pins a previous page
that supplied the parent event but is not written. -/
structure TopicPlan where
  stream : Digest
  cellId : Nat
  pre : LifecycleImage Registry
  post : EventPage
  entry : EventEntry
  guards : List ReadGuard

def TopicPlan.write (plan : TopicPlan) : DataWrite where
  cellId := ⟨plan.cellId⟩
  expectedPre := physicalRoot plan.pre
  exactPost := physicalRoot (.live (pageCell plan.post))
  canonicalPostBytes := LifecycleImage.bytes Registry (.live (pageCell plan.post))

def TopicPlan.freshIds (plan : TopicPlan) : List Nat :=
  match plan.pre with
  | .fresh => [plan.cellId]
  | _ => []

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
  ⟨Hyperdocument.deriveVersionEventId HyperdocumentEventPageMaterializer.eventPreimageCodec
    HyperdocumentEventPageMaterializer.eventDerivation record, record⟩

/-- Sequence `n` lives at page `(n-1)/4`, slot `(n-1)%4`. It is admitted only
as the stream's next position: every earlier slot of its page is occupied, its
own slot is empty, and a first slot beyond page zero follows a full previous
page. The parent is exactly the previous event. -/
def planTopic (deployment : Deployment) (directory : Directory Nat Registry)
    (domain : Digest) (payer : Nat) (publication : Publication)
    (author : Hyperdocument.PrincipalRef) (bookPre bookPost txId effect : Digest) :
    Except Reject TopicPlan := do
  let stream := streamDigest domain payer publication.topic
  let pageNumber := pageOf publication.sequence
  let slot := slotOf publication.sequence
  let cellId := pageCellId stream pageNumber
  let current ← requireSome .topicPageUnavailable (readPage deployment directory cellId)
  let (pre, prePage, parents, guards) ← match current with
    | .fresh =>
        if slot ≠ 0 then throw .sequenceGap
        else if pageNumber = 0 then
          pure ((.fresh : LifecycleImage Registry), emptyPage domain stream 0,
            ([] : List Hyperdocument.VersionEventId), ([] : List ReadGuard))
        else
          let previousId := pageCellId stream (pageNumber - 1)
          match readPage deployment directory previousId with
          | some (.live previousCell previousPage) =>
              if previousPage.document = ⟨stream⟩ ∧ previousPage.pageNumber = pageNumber - 1 then
                match previousPage.slot3 with
                | some last =>
                    pure (.fresh, emptyPage domain stream pageNumber, [last.key],
                      [⟨⟨previousId⟩, physicalRoot (.live previousCell)⟩])
                | none => throw .sequenceGap
              else throw .topicPageUnavailable
          | _ => throw .sequenceGap
    | .live cell page =>
        if page.document = ⟨stream⟩ ∧ page.pageNumber = pageNumber then
          if (slotAt page slot).isSome then throw .sequenceTaken
          else if slot = 0 ∨ !(filledBelow page slot) then throw .sequenceGap
          else
            match slotAt page (slot - 1) with
            | some previous => pure (.live cell, page, [previous.key], [])
            | none => throw .sequenceGap
        else throw .topicPageUnavailable
  let record := eventRecord domain stream publication.sequence
    (payloadDigest domain publication.payload) parents bookPre bookPost txId effect author
  let entry := eventEntry record
  pure ⟨stream, cellId, pre, withSlot prePage slot entry, entry, guards⟩

/-! ## Preparation, authorization, plan -/

structure Prepared {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (tariff : CreationTariff)
    (ambient : Ambient) (durable : Durable) (command : Command) where
  private mk ::
  shape : command.shapeOk = true
  feeExact : command.fee = tariff.base
  directory : LoadedDirectory durable
  authority : Loaded deployment.authorityAnchor durable.snapshot
  book : ResourceBirthController.Concrete.ObservedCell deployment directory.directory
    deployment.resourceBookId .resourceBook
  resources : CanonicalResourceKernel.AcceptedBatch book.payload (batch tariff command)
  topic : Option TopicPlan
  candidate : Candidate (family authority.snapshot profile.semantics ambient command)
    authority.snapshot.cell (declaration authority.snapshot profile.semantics command) ()
  update : CredentialAuthorityDomain.Prepared authority.snapshot
    (edits authority.snapshot (declaration authority.snapshot profile.semantics command))
  postExact : update.postLogical = candidate.validated.apply.logical
  physical : Lowered directory authority
    (edits authority.snapshot (declaration authority.snapshot profile.semantics command)) update
    ((topic.map TopicPlan.freshIds).getD [])
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
        if fresh : isNullified snapshot.cell d.operationNullifier = false then
          let update ← requireSome .authorityPreparation
            (CredentialAuthorityDomain.prepare snapshot (edits snapshot d))
          match validate AuthorityMaterializer snapshot.cell d.patch with
          | .rejected _ => throw .validation
          | .accepted validated =>
            if same : CredentialAuthorityStateCodec.encode update.postLogical =
                CredentialAuthorityStateCodec.encode validated.apply.logical then
              let physical ← requireSome .physicalPreparation
                (lower directory authority update ((topic.map TopicPlan.freshIds).getD []))
              let source ← requireSome .policyUnavailable (CanonicalCellRegistry.loadPolicySource
                snapshot.domain directory.directory
                (snapshot.authState.policyAddress ⟨command.payer⟩
                  (snapshot.authState.policyRevision ⟨command.payer⟩)))
              let candidate : Candidate (family snapshot profile.semantics ambient command)
                  snapshot.cell d () :=
                { preStateBound := rfl
                  modeEvidence := ⟨rfl, fresh⟩
                  validated := validated
                  postcondition := validated.resultAt }
              pure ⟨shape, feeExact, directory, authority, book, resources, topic, candidate,
                update, CredentialAuthorityStateCodec.encode_injective same, physical, source⟩
            else throw .refinement
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
    (logical : LogicalState CredentialAuthorityState.schema.{0, 0}) : Minidregg.Pred.State :=
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

/-- The stream head: the highest occupied sequence, found by walking pages
from zero until an unoccupied slot. Bounded by `maxPages` page reads. -/
def streamHead (deployment : Deployment) (directory : Directory Nat Registry)
    (stream : Digest) (maxPages : Nat) : Nat :=
  let rec walk : Nat → Nat → Nat
    | 0, _ => 0
    | fuel + 1, pageNumber =>
        match readPage deployment directory (pageCellId stream pageNumber) with
        | some (.live _ page) =>
            let count := (List.range pageCapacity).countP fun slot => (slotAt page slot).isSome
            if count = pageCapacity then walk fuel (pageNumber + 1)
            else pageNumber * pageCapacity + count
        | _ => pageNumber * pageCapacity
  walk maxPages 0

/-- Events of one stream with sequence strictly above `cursor`, in order, at
most `limit` of them. Only occupied slots are returned; a gap ends the read. -/
def eventsSince (deployment : Deployment) (directory : Directory Nat Registry)
    (stream : Digest) (cursor limit : Nat) : List EventEntry :=
  let rec collect : Nat → Nat → List EventEntry → List EventEntry
    | 0, _, acc => acc.reverse
    | fuel + 1, sequence, acc =>
        if acc.length ≥ limit then acc.reverse else
        match readPage deployment directory (pageCellId stream (pageOf sequence)) with
        | some (.live _ page) =>
            match slotAt page (slotOf sequence) with
            | some entry => collect fuel (sequence + 1) (entry :: acc)
            | none => acc.reverse
        | _ => acc.reverse
  collect (limit + 1) (cursor + 1) []

end Minidregg.Kernel.FleetTurn
