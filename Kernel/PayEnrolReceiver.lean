/-
# Kernel.PayEnrolReceiver — one enrollment-index payment is one turn (PAY §11.4, P3b-2)

The observer submits one finalized transfer to the enrollment index
(`Tariff.enrolIndex`) as a signed `Command`.  The receiver parses its memo,
runs the pinned native verifier on both signatures
(`PayEnrolSignatureIO.verifyNative`; a verifier failure REFUSES, it never
journals), decides with `PayEnrolDecision.decideEnrol`, and installs ONE
durable intent:

* **enrol** — writes the authority cell, the factory, the Book, the new
  account's cell, the new account law's source cell and the pay cell:
  - authority: the Mini key as a new subject `subjectOf miniKey`
    (`keyEntries`), the account's two owner grants and initial law (an
    ordinary resource birth's grant batch, `ResourceBirthAuthority.entries`),
    and one factory-observation grant (`observeObject` on the factory, the M3
    provisioning grant);
  - the account birth through the resource-birth controller's own preparation
    (`allocate?`, `BirthsAdmissible`, `TemplateBound`, `PhysicalPostLaw`): a
    declared account owned by the new subject;
  - Book: `mint credit` to the enrollment float, the lease (`weeks · weekCredit`)
    and the birth fee to the tariff's collector, the remainder to the new
    account — the float ends where it started;
  - pay cell: `enrolment[miniKey]`, `sshIndex[blob]`,
    `assignment[nextFree] := account`;
  - clock cell: `slot := tip.slot`, `now` to the tip's block time when later
    (`PayObservation.advanceClock`), as an observation report does.
* **renew** — writes the Book (mint to the float, the lease to the collector,
  the remainder to the friend's account), the pay cell (the enrolment row's
  `leaseUntil`) and the clock cell.  Nothing else.
* **journal** — writes the pay cell (`journal[nullifier]`) and the clock cell.
  Nothing is minted.

Every branch spends the transfer's nullifier `soltx:‖sig‖addr` and the tip's
tick nullifier, exactly as P3's report; the enrol branch also spends the birth
identity's authority marker.

Authorization: the observer signs a capability-mode request of kind
`program`, target and policy the FACTORY, verb `installPolicy`, presenting
`C_enrol`; the factory's law sees the slot `authority/operation/pay-self-enrol`
= 1 (`NativeHostGenesis.confinedFactoryLaw`).  The effect digest commits to the
command bytes, the decision and (enrol) the exact birth descriptor.

One intent writing several cells is the existing mechanism: a `DataIntent`'s
writes are a list over cells and `DurableDataIntent.execute` installs all of
them or none (`multi_cell_intent_atomic`, below).  A resource birth already
writes allocations, the factory, the Book and the authority cell in one intent
(`ResourceBirthController.Concrete.planWrites`); this receiver uses that same
write plan and appends the pay cell.
-/
import Kernel.ClockCellDomain
import Kernel.PayObservationReceiver
import Kernel.PayChainTip
import Kernel.PayEnrolDecision
import Kernel.ParticipantKeyEnrollment
import Kernel.NativeHostGenesis
import Compiler.PayEnrolSignatureIO

namespace Minidregg.Kernel.PayEnrolReceiver

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.CredentialAuthorityEntryCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.PayCell
open Minidregg.Kernel.PayTariff
open Minidregg.Kernel.PayEnrolMemo
open Minidregg.Kernel.PayEnrolDecision
open Minidregg.Kernel.PayObservation (Observation nullifier tickNullifier nullifierBytes
  observationStream)
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialAuthorityEffects
open Minidregg.Theory.CredentialSigningKey
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.PolicyInstall
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.Store (Store Patch Op Address)
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

attribute [local irreducible] CanonicalRuntimeProfile.Profile.compilerProfile

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev Snapshot := CredentialAuthorityDomain.Snapshot
abbrev AuthorityMaterializer := CredentialAuthorityCell.materializer
abbrev BookCell (deployment : Deployment) (directory : Directory Nat Registry) :=
  ResourceBirthController.Concrete.ObservedCell deployment directory deployment.resourceBookId
    .resourceBook
abbrev FactoryCell (deployment : Deployment) (directory : Directory Nat Registry) :=
  ResourceBirthController.Concrete.ObservedCell deployment directory deployment.factoryId
    .declaredObject

/-! ## Command and ingress -/

/-- The observer's submission of one enrollment-index transfer: the watcher's
record, the finalized tip it was read at, and the two roots the observer read. -/
structure Command where
  observer : SubjectId
  /-- `C_enrol`, the observer's capability on the factory. -/
  capability : CapabilityId
  nonce : Nat
  expectedAuthorityRoot : Digest
  expectedPayRoot : Digest
  tip : ChainTip
  observation : Observation
  deriving DecidableEq, Repr

def commandStream : StreamCodec Command :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product capabilityIdStream
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product digestStream
            (StreamCodec.product digestStream
              (StreamCodec.product chainTipStream observationStream))))))
    (fun c => (c.observer, c.capability, c.nonce, c.expectedAuthorityRoot, c.expectedPayRoot,
      c.tip, c.observation))
    (fun (observer, capability, nonce, authorityRoot, payRoot, tip, observation) =>
      ⟨observer, capability, nonce, authorityRoot, payRoot, tip, observation⟩)
    (by intro c; cases c; rfl)

def commandFrame : List UInt8 := "DREGG/PAY/SELF-ENROL/v1".toUTF8.toList

def commandCodec : LawfulCodec Command := framed commandFrame commandStream

theorem command_roundtrip (command : Command) :
    commandCodec.decode (commandCodec.encode command) = some command :=
  commandCodec.decode_encode command

theorem command_canonical {bytes : List UInt8} {command : Command}
    (accepted : commandCodec.decode bytes = some command) : commandCodec.encode command = bytes :=
  framed_canonical commandFrame commandStream accepted

def ingressFrame : List UInt8 := "DREGG/PAY/SELF-ENROL/SIGNED/v1".toUTF8.toList

def ingressCodec : LawfulCodec PayObservation.Ingress :=
  framed ingressFrame PayObservation.ingressStream

theorem ingress_canonical {bytes : List UInt8} {ingress : PayObservation.Ingress}
    (accepted : ingressCodec.decode bytes = some ingress) : ingressCodec.encode ingress = bytes :=
  framed_canonical ingressFrame PayObservation.ingressStream accepted

structure DecodedIngress where
  private mk ::
  ingress : PayObservation.Ingress
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
    match envelopeExact : CredentialSignatureAdmission.canonicalEnvelopeCodec.decode
        ingress.envelope with
    | none => none
    | some envelope =>
      some ⟨ingress, command, command_canonical commandExact, envelope, envelopeExact⟩

def DecodedIngress.bytes (ingress : DecodedIngress) : List UInt8 :=
  ingressCodec.encode ingress.ingress

def marker (domain semantics : Digest) (command : Command) : Nat :=
  (Sp800185Cshake256.hash "DREGG.PAY.SELF-ENROL.IDENTITY/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
        StreamCodec.nat))).encode
      (domain, semantics, command.observer, command.nonce))).digest.value

/-! ## Identities derived from the Mini key

Every identifier the enrollment creates is a function of the deployment's
domain and the 32-byte Mini key, so a replay derives the same ones and no
caller chooses them.  The subject is P3b-1's `subjectOf`.  A collision with an
existing identifier refuses at preparation (allocation, grant freshness, key
freshness); nothing is consumed. -/

def deriveId (tag : String) (domain : Digest) (miniKey : List UInt8) : Nat :=
  (Sp800185Cshake256.hash ("DREGG.PAY.SELF-ENROL." ++ tag ++ "/v1").toUTF8.toList
    (digestStream.encode domain ++ miniKey)).digest.value % 2 ^ 64

structure Ids where
  subject : Nat
  account : Nat
  ownerCapability : Nat
  controlCapability : Nat
  observeCapability : Nat
  keyId : Nat
  deriving DecidableEq, Repr

def ids (domain : Digest) (miniKey : List UInt8) : Ids :=
  ⟨subjectOf miniKey, deriveId "ACCOUNT" domain miniKey, deriveId "OWNER" domain miniKey,
    deriveId "CONTROL" domain miniKey, deriveId "OBSERVE" domain miniKey,
    deriveId "KEY-ID" domain miniKey⟩

/-- The new subject's signing key: the Mini key, Ed25519, active from the
current authority revision with no expiry of its own (the lease gates the
login, not the key). -/
def keyEpoch : Nat := 1
/-- K-PREROTATE: a self-enrolled key commits to NO next key. The payment memo
carries the Mini key alone, so the subject it makes is the `--no-prerotation`
kind: it can never rotate (`SubjectKeyRotation` refuses `notPrerotated`); a
stolen key is replaced by enrolling a new subject, exactly as before
pre-rotation. Committing a next key here needs it in the memo (a pay-memo
format change, task opened at the merge). -/
def selfEnrolNextKey : Option TypedAuthorization.Digest := none
def keyLifetime : Nat := 2 ^ 62

def keyRecord (revision : Nat) (identities : Ids) (miniKey : List UInt8) : KeyRecord :=
  ⟨identities.keyId, keyEpoch, CredentialSignatureAdmission.ed25519Algorithm, identities.subject,
    miniKey, revision, revision + keyLifetime, selfEnrolNextKey⟩

/-! ## The birth of the account, as an ordinary birth descriptor -/

/-- The account's own law: only its owner acts on it. -/
def accountPredicate (subject : Nat) : Minidregg.Pred.Pred :=
  .all [.eq "request/subject" (Int.ofNat subject)]

def accountPolicy (deployment : Deployment) (semantics : Digest) (identities : Ids) :
    PolicyRecord where
  policyId := ⟨identities.account⟩
  version := 0
  domain := deployment.domain
  semantics := semantics
  previous := none
  predicate := accountPredicate identities.subject
  localSelector := {}
  parents := []
  descendants := none
  audience := none
  objectDescriptor := none

/-- A root capability exactly as genesis and birth authoring build one: the
template's issuer, budget and lifetime, the issuer and policy epochs current in
the loaded authority cell. -/
def rootCapability {kind : ResourceKind} (template : CanonicalRuntimeProfile.FactoryTemplate)
    (cell : CredentialAuthorityDomain.Cell) (height : Height) (identifier holder target : Nat)
    (verbs : Finset (Verb kind)) : Capability kind where
  id := ⟨identifier⟩
  root := ⟨identifier⟩
  parent := none
  issuer := template.issuer
  holder := .subject ⟨holder⟩
  scope := ⟨.explicit {⟨target⟩}, verbs, template.ownerBudget, none, ∅⟩
  notBefore := height
  notAfter := height + template.lifetime
  issuerEpoch := issuerEpochAt cell template.issuer
  policyId := ⟨target⟩
  policyEpoch := policyEpochAt cell ⟨target⟩
  ancestors := ∅
  channels := ∅

def ownerGrant (template : CanonicalRuntimeProfile.FactoryTemplate)
    (cell : CredentialAuthorityDomain.Cell) (height : Height) (identities : Ids) : AuthorityGrant :=
  ⟨.account, ⟨rootCapability template cell height identities.ownerCapability identities.subject
    identities.account (ResourceBirthPolicyController.Concrete.ownerVerbs .account), []⟩⟩

def controlGrant (template : CanonicalRuntimeProfile.FactoryTemplate)
    (cell : CredentialAuthorityDomain.Cell) (height : Height) (identities : Ids) : AuthorityGrant :=
  ⟨.program, ⟨rootCapability template cell height identities.controlCapability identities.subject
    identities.account {.installPolicy, .revokeCapability}, []⟩⟩

/-- The factory-observation grant (M3's provisioning grant): `observeObject`
on the factory, held by the new subject. -/
def observeGrant (deployment : Deployment) (template : CanonicalRuntimeProfile.FactoryTemplate)
    (cell : CredentialAuthorityDomain.Cell) (height : Height) (identities : Ids) : AuthorityGrant :=
  ⟨.object, ⟨rootCapability template cell height identities.observeCapability identities.subject
    deployment.factoryId {.observeObject}, []⟩⟩

def birthItem (identities : Ids) : BirthItem Registry :=
  ⟨⟨identities.account, CellSlot.root Registry .absent,
    NativeHostGenesis.declaredPacked identities.account true (.closed [])⟩, .account, ⟨identities.subject⟩, none, none⟩

def initialPolicy (deployment : Deployment) (semantics : Digest) (identities : Ids) :
    InitialPolicy :=
  let rule := accountPolicy deployment semantics identities
  ⟨rule.policyId, PolicyRecordCodec.digest rule, PolicyRecordCodec.encode rule⟩

/-- The birth identity: creator = the new subject, nonce 0.  One enrollment
per subject, so one birth per identity. -/
def birthIdentity (deployment : Deployment) (semantics : Digest) (identities : Ids) : Digest :=
  CredentialAuthorityReplay.birthIdentity deployment.domain semantics ⟨deployment.factoryId⟩
    ⟨identities.subject⟩ 0

/-- The account birth, priced by the factory tariff and funded from the float.
`auxiliaryCreates` is filled by preparation (the policy source cell). -/
def draft (deployment : Deployment) (semantics : Digest)
    (template : CanonicalRuntimeProfile.FactoryTemplate) (tariff : CreationTariff)
    (cell : CredentialAuthorityDomain.Cell) (height : Height) (identities : Ids)
    (float funding : Nat) : Descriptor Registry :=
  let identity := birthIdentity deployment semantics identities
  let base : Descriptor Registry :=
    { factory := ⟨deployment.factoryId⟩, creator := ⟨identities.subject⟩,
      transactionId := identity, nonce := 0, births := [birthItem identities],
      auxiliaryCreates := [],
      grants := [ownerGrant template cell height identities,
        controlGrant template cell height identities],
      initialPolicies := [initialPolicy deployment semantics identities],
      authorityNullifier := identity.value,
      funding := [⟨float, identities.account, tariff.asset, funding⟩],
      fee := ⟨float, tariff.collector, tariff.asset, 0⟩ }
  { base with fee := { base.fee with amount := base.quotedFee tariff } }

/-- The birth fee does not depend on the funding: it prices the births, the
grants and the initial payload bytes only. -/
theorem draft_fee_funding_free (deployment : Deployment) (semantics : Digest)
    (template : CanonicalRuntimeProfile.FactoryTemplate) (tariff : CreationTariff)
    (cell : CredentialAuthorityDomain.Cell) (height : Height) (identities : Ids)
    (float funding funding' : Nat) :
    (draft deployment semantics template tariff cell height identities float funding).fee =
      (draft deployment semantics template tariff cell height identities float funding').fee := rfl

def birthFee (deployment : Deployment) (semantics : Digest)
    (template : CanonicalRuntimeProfile.FactoryTemplate) (tariff : CreationTariff)
    (cell : CredentialAuthorityDomain.Cell) (height : Height) (identities : Ids) (float : Nat) :
    Nat :=
  (draft deployment semantics template tariff cell height identities float 0).fee.amount

/-! ## The value legs -/

/-- What a granted lease costs: every week granted is paid for. -/
def leaseCost (tariff : Tariff) (weeks : Nat) : Nat := weeks * tariff.weekCredit

/-- The friend's remainder after the birth fee and the lease (enrollment). -/
def enrolRemainder (tariff : Tariff) (price : Price) (plan : EnrolPlan) : Nat :=
  plan.credit - price.birthFee - leaseCost tariff plan.weeks

/-- The friend's remainder after the lease (renewal). -/
def renewRemainder (tariff : Tariff) (plan : RenewPlan) : Nat :=
  plan.credit - leaseCost tariff plan.weeks

/-- The enrollment's Book batch: the new account registered, the credit
minted to the float, the lease paid to the collector, then the birth's own
funding (the remainder) and fee, in the birth descriptor's order. -/
def enrolBatch (tariff : Tariff) (collector : Nat) (plan : EnrolPlan)
    (descriptor : Descriptor Registry) : CanonicalResourceKernel.Batch :=
  ⟨descriptor.resourceBatch.registrations,
    .mint tariff.asset plan.float plan.credit ::
      .fee plan.float collector tariff.asset (leaseCost tariff plan.weeks) ::
        descriptor.resourceBatch.operations⟩

def renewBatch (tariff : Tariff) (collector : Nat) (plan : RenewPlan) :
    CanonicalResourceKernel.Batch :=
  ⟨[], [.mint tariff.asset plan.float plan.credit,
    .fee plan.float collector tariff.asset (leaseCost tariff plan.weeks),
    .transfer plan.float plan.account tariff.asset (renewRemainder tariff plan)]⟩

/-! ## The authority delta of an enrollment -/

/-- Every authority entry an enrollment sets: the birth's grant batch (the
account law and its two owner grants), the new subject's key, and the
factory-observation grant, each grant and the key with the registration of
its own revocation key (a capability is live only while registered and not
revoked). -/
def authorityEntries (descriptor : Descriptor Registry) (key : KeyRecord)
    (observe : AuthorityGrant) : List (Minidregg.Theory.Store.Entry CredentialAuthorityState.layout) :=
  ResourceBirthAuthority.entries descriptor ++ NativeHostGenesis.keyEntries key ++
    [ResourceBirthAuthority.grantEntry observe, ResourceBirthAuthority.grantRegistrationEntry observe]

/-! ## The pay-cell patch of each decision -/

/-- The decision's own rows (the clock is the clock cell's, written beside). -/
def payPatch (o : Observation) (decision : Decision) (account : Nat)
    (record : Option EnrolRecord) : Patch PayCell.layout :=
    match decision with
    | .enrol plan => plan.patch account o.slot
    | .renew plan => match record with
        | some record => plan.patch record
        | none => []
    | .journal reason => journalPatch o reason

/-! ## The decision's committed bytes -/

def memoBytes (memo : Memo) : List UInt8 := bytesStream.encode (PayEnrolMemo.encode memo)

def decisionBytes : Decision → List UInt8
  | .enrol plan => [1] ++ memoBytes plan.memo ++ StreamCodec.nat.encode plan.float ++
      StreamCodec.nat.encode plan.credit ++ StreamCodec.nat.encode plan.weeks ++
      (StreamCodec.option StreamCodec.nat).encode plan.index ++ StreamCodec.nat.encode plan.leaseUntil
  | .renew plan => [2] ++ memoBytes plan.memo ++ StreamCodec.nat.encode plan.float ++
      StreamCodec.nat.encode plan.account ++ StreamCodec.nat.encode plan.credit ++
      StreamCodec.nat.encode plan.weeks ++ StreamCodec.nat.encode plan.leaseFrom ++
      StreamCodec.nat.encode plan.leaseUntil
  | .journal reason => [3] ++ StreamCodec.nat.encode reason.code

def decisionTag : Decision → Nat
  | .enrol _ => 1
  | .renew _ => 2
  | .journal _ => 3

/-- What the observer's signature binds beyond the command: the decision and,
for an enrollment, the exact birth descriptor. -/
structure Declaration where
  decision : List UInt8
  birth : List UInt8
  expectedPreRoot : Digest
  operationNullifier : Nat

def declarationStream : StreamCodec Declaration :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream
      (StreamCodec.product digestStream StreamCodec.nat)))
    (fun d => (d.decision, d.birth, d.expectedPreRoot, d.operationNullifier))
    (fun (decision, birth, root, nullifier) => ⟨decision, birth, root, nullifier⟩)
    (by intro d; cases d; rfl)

def declarationCodec : LawfulCodec Declaration :=
  ResourceBirthCodec.strictCodec declarationStream.toLawful

structure Mode {M : Materializer PayCell.layout Digest} (pre : Materialized M) (d : Declaration) : Type where
  rootExact : d.expectedPreRoot = pre.root

def effectDigest (domain semantics : Digest) (command : Command) (d : Declaration) : Digest :=
  (Sp800185Cshake256.hash "DREGG.PAY.SELF-ENROL.EFFECT/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product bytesStream bytesStream))).encode
      (domain, semantics, commandCodec.encode command, declarationCodec.encode d))).digest

/-- The environment of a submission: the federation, the logical height, and
the factory's creation tariff (the birth fee's source). -/
structure Ambient where
  federation : FederationId
  height : Height
  tariff : CreationTariff

def context (deployment : Deployment) (snapshot : Snapshot) (semantics : Digest)
    (ambient : Ambient) (command : Command) : RequestContext where
  authority :=
    { kind := .program
      domain := snapshot.domain
      semantics := semantics
      federation := ambient.federation
      subject := command.observer
      subjectKeyEpoch := snapshot.authState.subjectKeyEpoch command.observer
      target := ⟨deployment.factoryId⟩
      verb := .installPolicy
      nonce := marker snapshot.domain semantics command
      height := ambient.height
      policyId := ⟨deployment.factoryId⟩
      policyEpoch := snapshot.authState.policyEpoch ⟨deployment.factoryId⟩
      policyRevision := snapshot.authState.policyRevision ⟨deployment.factoryId⟩
      cost := (commandCodec.encode command).length }
  argsDigestBytes := fun bytes =>
    (Sp800185Cshake256.hash "DREGG.PAY.SELF-ENROL.ARGS/v1".toUTF8.toList
      (commandCodec.encode command ++ bytes)).digest

def request (deployment : Deployment) (snapshot : Snapshot) (pay : PayCell.Cell) (semantics : Digest)
    (ambient : Ambient) (command : Command) (d : Declaration) : Request .program :=
  ((context deployment snapshot semantics ambient command).request declarationCodec
    (effectDigest snapshot.domain semantics command) pay.root d.operationNullifier d).2

def family (deployment : Deployment) (snapshot : Snapshot) (pay : PayCell.Cell) (semantics : Digest)
    (ambient : Ambient) (command : Command) (patch : Patch PayCell.layout) :
    SemanticEffectFamily PayCell.layout PayCell.materializer Nat where
  Declaration := Declaration
  declarationCodec := declarationCodec
  pre := pay
  request := fun d => (context deployment snapshot semantics ambient command).request
    declarationCodec (effectDigest snapshot.domain semantics command) pay.root
    d.operationNullifier d
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun d _ => Mode pay d
  Postcondition := fun _ _ post => patch.ResultAt pay.logical post
  effectDigest := effectDigest snapshot.domain semantics command
  patch := fun _ _ => patch
  nullifier := fun d _ => some d.operationNullifier
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

/-! ## Refusals -/

inductive Reject where
  | malformedIngress | directoryUnavailable | authorityUnavailable | payUnavailable
  | bookUnavailable | factoryUnavailable | staleAuthority | stalePay
  | clockUnavailable | tipBehindClock | chainTipRegressed
  | decision (reason : PayEnrolDecision.Reject)
  /-- The native verifier failed: the payment is refused, never journaled. -/
  | verifier (error : CredentialSignatureIO.Error)
  | grantBatch | birthShape | keyTaken | observeGrantTaken | authorityEntries
  | allocation | bookAdmission | renewalRecord
  | validation | physicalPreparation
  | policyUnavailable | capabilityRejected | policyRejected | policyInputRange | policyCastAlias
  | signature (reason : CredentialSignatureAdmission.Reject)
  deriving Repr

def requireSome {A : Type} (reason : Reject) : Option A → Except Reject A
  | none => .error reason
  | some value => .ok value

def require (condition : Prop) [Decidable condition] (reason : Reject) :
    Except Reject (PLift condition) :=
  if holds : condition then .ok ⟨holds⟩ else .error reason

/-! ## What the decision reads -/

/-- The memo the observation carries, when it parses. -/
def parsedMemo (o : Observation) : Option Memo :=
  match o.memo with
  | .present bytes => match parse bytes with
      | .ok memo => some memo
      | .error _ => none
  | _ => none

/-- Whether the authority cell already has a subject at the Mini key's derived
subject.  A self-enrolled key reaches renewal through its pay-cell row first. -/
def subjectTakenIn (snapshot : Snapshot) (o : Observation) : Bool :=
  match parsedMemo o with
  | some memo =>
      (show Option Epoch from snapshot.logical ⟨.subjectKeyEpoch, ⟨subjectOf memo.miniKey⟩⟩).isSome
  | none => false

/-- The birth fee for the key the memo names (the fee prices the account
birth, its two grants and its initial payload bytes). -/
def priceIn (deployment : Deployment) (semantics : Digest)
    (template : CanonicalRuntimeProfile.FactoryTemplate) (ambient : Ambient)
    (snapshot : Snapshot) (o : Observation) : Price :=
  match parsedMemo o with
  | some memo => ⟨birthFee deployment semantics template ambient.tariff snapshot.cell ambient.height
      (ids deployment.domain memo.miniKey) 0⟩
  | none => ⟨0⟩

/-- Every key-registry freshness the interactive enrollment checks
(`ParticipantKeyEnrollment.prepare`): no key epoch or key record at the
subject, and no key anywhere with its subject, key id or public key. -/
def KeyFresh (snapshot : Snapshot) (key : KeyRecord) : Prop :=
  (show Option Epoch from snapshot.logical ⟨.subjectKeyEpoch, ⟨key.subject⟩⟩) = none ∧
  (show Option KeyRecord from snapshot.logical ⟨.subjectKey, (⟨key.subject⟩, key.keyEpoch)⟩) = none ∧
  ParticipantKeyEnrollment.allKeys snapshot.logical (fun k => k.subject != key.subject) = true ∧
  ParticipantKeyEnrollment.allKeys snapshot.logical (fun k => k.keyId != key.keyId) = true ∧
  ParticipantKeyEnrollment.allKeys snapshot.logical (fun k => k.publicKey != key.publicKey) = true

instance keyFreshDecidable (snapshot : Snapshot) (key : KeyRecord) : Decidable (KeyFresh snapshot key) := by
  unfold KeyFresh
  infer_instance

/-! ## Preparation of the legs -/

section Legs

variable {F : Type} [Field F] (deployment : Deployment)
  (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) {durable : Durable}

def enrolIds (plan : EnrolPlan) : Ids := ids deployment.domain plan.memo.miniKey

def enrolKey (authority : Loaded deployment durable.snapshot) (plan : EnrolPlan) : KeyRecord :=
  keyRecord authority.snapshot.revision (enrolIds deployment plan) plan.memo.miniKey

def enrolObserve (authority : Loaded deployment durable.snapshot) (plan : EnrolPlan) :
    AuthorityGrant :=
  observeGrant deployment profile.template authority.snapshot.cell ambient.height
    (enrolIds deployment plan)

def enrolDraft (authority : Loaded deployment durable.snapshot) (tariff : Tariff) (price : Price)
    (plan : EnrolPlan) : Descriptor Registry :=
  draft deployment profile.semantics profile.template ambient.tariff authority.snapshot.cell
    ambient.height (enrolIds deployment plan) plan.float (enrolRemainder tariff price plan)

/-- Every leg of an enrollment, prepared on the loaded image before any
authorization.  The descriptor is the ordinary birth draft of
`enrolDraft` with the preparation's own auxiliary creates (the account law's
source cell); the authority post is ONE patch over the loaded cell. -/
structure EnrolLegs (directory : LoadedDirectory durable)
    (authority : Loaded deployment durable.snapshot) (book : BookCell deployment directory.directory)
    (tariff : Tariff) (price : Price) (plan : EnrolPlan) where
  private mk ::
  descriptor : Descriptor Registry
  descriptorExact : descriptor =
    { enrolDraft deployment profile ambient authority tariff price plan with
      auxiliaryCreates := descriptor.auxiliaryCreates }
  grants : PreparedGrantBatch profile.compilerProfile deployment authority descriptor
  auxiliaryExact : descriptor.auxiliaryCreates = grants.auxiliaryCreates
  initials : CanonicalCellRegistry.BirthsAdmissible deployment descriptor
  templateBound : ResourceBirthPolicyController.Concrete.TemplateBound profile.template
    authority.snapshot.authState ambient.height descriptor
  bornLineage : ResourceBirthPolicyController.Concrete.BornLineage
    (ResourceBirthPolicyController.Concrete.placementLineage authority.snapshot.cell) descriptor
  keyFresh : KeyFresh authority.snapshot (enrolKey deployment authority plan)
  observeReady : GrantReady authority.snapshot (enrolObserve deployment profile ambient authority plan)
  entriesDistinct : ((authorityEntries descriptor (enrolKey deployment authority plan)
    (enrolObserve deployment profile ambient authority plan)).map Sigma.fst).Nodup
  authorityValidated : ValidatedPatch AuthorityMaterializer authority.snapshot.cell
    authority.snapshot.cell.root
    (assignAll authority.snapshot.logical (authorityEntries descriptor
      (enrolKey deployment authority plan) (enrolObserve deployment profile ambient authority plan)))
  allocated : ResourceBirthController.Allocated Registry directory.directory descriptor
  resources : CanonicalResourceKernel.AcceptedBatch book.payload
    (enrolBatch tariff ambient.tariff.collector plan descriptor)

def prepareEnrolLegs (directory : LoadedDirectory durable)
    (authority : Loaded deployment durable.snapshot) (book : BookCell deployment directory.directory)
    (tariff : Tariff) (price : Price) (plan : EnrolPlan) :
    Except Reject (EnrolLegs deployment profile ambient directory authority book tariff price plan) := do
  let base := enrolDraft deployment profile ambient authority tariff price plan
  let first ← requireSome .grantBatch
    (prepareGrantBatch profile.compilerProfile deployment authority base)
  let descriptor : Descriptor Registry := { base with auxiliaryCreates := first.auxiliaryCreates }
  let grants ← requireSome .grantBatch
    (prepareGrantBatch profile.compilerProfile deployment authority descriptor)
  let aux ← require (ResourceBirthController.Concrete.sameCreates descriptor.auxiliaryCreates
    grants.auxiliaryCreates = true) .grantBatch
  let initials ← require (CanonicalCellRegistry.BirthsAdmissible deployment descriptor) .birthShape
  let template ← require (ResourceBirthPolicyController.Concrete.TemplateBound profile.template
    authority.snapshot.authState ambient.height descriptor) .birthShape
  let lineage ← require (ResourceBirthPolicyController.Concrete.BornLineage
    (ResourceBirthPolicyController.Concrete.placementLineage authority.snapshot.cell) descriptor) .birthShape
  let key ← require (KeyFresh authority.snapshot (enrolKey deployment authority plan)) .keyTaken
  let observe ← require (GrantReady authority.snapshot
    (enrolObserve deployment profile ambient authority plan)) .observeGrantTaken
  let distinct ← require (((authorityEntries descriptor (enrolKey deployment authority plan)
    (enrolObserve deployment profile ambient authority plan)).map Sigma.fst).Nodup) .authorityEntries
  match validate AuthorityMaterializer authority.snapshot.cell authority.snapshot.cell.root
      (assignAll authority.snapshot.logical (authorityEntries descriptor
        (enrolKey deployment authority plan) (enrolObserve deployment profile ambient authority plan)))
      with
  | .rejected _ => throw .validation
  | .accepted validated =>
    let allocated ← match ResourceBirthController.allocate? Registry directory.directory descriptor with
      | .error _ => throw .allocation
      | .ok allocated => pure allocated
    let admission ← require ((enrolBatch tariff ambient.tariff.collector plan descriptor).Admission
      (CanonicalResourceKernel.logicalBook book.payload.logical)) .bookAdmission
    pure ⟨descriptor, rfl, grants, (ResourceBirthController.Concrete.sameCreates_iff _ _).mp aux.down,
      initials.down, template.down, lineage.down, key.down, observe.down,
      distinct.down, validated, allocated,
      CanonicalResourceKernel.AcceptedBatch.ofAdmission admission.down⟩

/-- The authority cell after the enrollment. -/
def EnrolLegs.authorityPost {directory : LoadedDirectory durable}
    {authority : Loaded deployment durable.snapshot} {book : BookCell deployment directory.directory}
    {tariff : Tariff} {price : Price} {plan : EnrolPlan}
    (legs : EnrolLegs deployment profile ambient directory authority book tariff price plan) :
    CredentialAuthorityDomain.Cell :=
  legs.authorityValidated.apply

/-- The legs of each decision. -/
inductive Legs (directory : LoadedDirectory durable) (authority : Loaded deployment durable.snapshot)
    (pay : PayCellDomain.Loaded deployment durable.snapshot)
    (book : BookCell deployment directory.directory) (tariff : Tariff) (price : Price) :
    Decision → Type
  | enrol (plan : EnrolPlan)
      (legs : EnrolLegs deployment profile ambient directory authority book tariff price plan) :
      Legs directory authority pay book tariff price (.enrol plan)
  | renew (plan : RenewPlan) (record : EnrolRecord)
      (recordExact : enrolmentAt pay.cell.logical plan.memo.miniKey = some record)
      (resources : CanonicalResourceKernel.AcceptedBatch book.payload
        (renewBatch tariff ambient.tariff.collector plan)) :
      Legs directory authority pay book tariff price (.renew plan)
  | journal (reason : JournalReason) : Legs directory authority pay book tariff price (.journal reason)

def prepareLegs (directory : LoadedDirectory durable)
    (authority : Loaded deployment durable.snapshot)
    (pay : PayCellDomain.Loaded deployment durable.snapshot)
    (book : BookCell deployment directory.directory) (tariff : Tariff) (price : Price) :
    (decision : Decision) →
      Except Reject (Legs deployment profile ambient directory authority pay book tariff price decision)
  | .enrol plan => do
      let legs ← prepareEnrolLegs deployment profile ambient directory authority book tariff price plan
      pure (.enrol plan legs)
  | .renew plan =>
      match recordExact : enrolmentAt pay.cell.logical plan.memo.miniKey with
      | none => .error .renewalRecord
      | some record =>
        if admission : (renewBatch tariff ambient.tariff.collector plan).Admission
            (CanonicalResourceKernel.logicalBook book.payload.logical) then
          .ok (.renew plan record recordExact
            (CanonicalResourceKernel.AcceptedBatch.ofAdmission admission))
        else .error .bookAdmission
  | .journal reason => .ok (.journal reason)

variable {deployment profile ambient}
variable {directory : LoadedDirectory durable} {authority : Loaded deployment durable.snapshot}
  {pay : PayCellDomain.Loaded deployment durable.snapshot}
  {book : BookCell deployment directory.directory} {tariff : Tariff} {price : Price}

/-- The new account (enrollment) — the account the pay patch assigns. -/
def Legs.account : {decision : Decision} →
    Legs deployment profile ambient directory authority pay book tariff price decision → Nat
  | _, .enrol plan _ => (enrolIds deployment plan).account
  | _, .renew _ record _ _ => record.account
  | _, .journal _ => 0

def Legs.record : {decision : Decision} →
    Legs deployment profile ambient directory authority pay book tariff price decision →
      Option EnrolRecord
  | _, .renew _ record _ _ => some record
  | _, _ => none

/-- The exact birth descriptor bytes an enrollment's signature binds. -/
def Legs.birthBytes : {decision : Decision} →
    Legs deployment profile ambient directory authority pay book tariff price decision →
      List UInt8
  | _, .enrol _ legs => CanonicalCellRegistry.sourceEncoding.codec.encode legs.descriptor
  | _, _ => []

/-- The cells each decision writes besides the pay cell. -/
def Legs.writes (factory : FactoryCell deployment directory.directory) : {decision : Decision} →
    Legs deployment profile ambient directory authority pay book tariff price decision →
      List DataWrite
  | _, .enrol _ legs =>
      ResourceBirthController.Concrete.planWrites deployment legs.descriptor factory.payload
        book.payload legs.resources.post (authority.writes legs.authorityPost)
  | _, .renew _ _ _ resources =>
      [ResourceBirthController.Concrete.packedWrite deployment.resourceBookId
        ⟨.resourceBook, book.payload⟩ ⟨.resourceBook, resources.post⟩]
  | _, .journal _ => []

/-- The enrollment also spends its birth identity's authority marker. -/
def Legs.nullifiers : {decision : Decision} →
    Legs deployment profile ambient directory authority pay book tariff price decision →
      List StableNullifier
  | _, .enrol _ legs =>
      [CredentialAuthorityReplay.nullifier deployment.domain legs.descriptor.authorityNullifier]
  | _, _ => []

end Legs

/-! ## Preparation -/

section Preparation

variable {F : Type} [Field F]

def declarationOf {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {directory : LoadedDirectory durable}
    {authority : Loaded deployment durable.snapshot}
    {pay : PayCellDomain.Loaded deployment durable.snapshot}
    {book : BookCell deployment directory.directory} {tariff : Tariff} {price : Price}
    (command : Command) {decision : Decision}
    (legs : Legs deployment profile ambient directory authority pay book tariff price decision) :
    Declaration :=
  ⟨decisionBytes decision, legs.birthBytes, command.expectedPayRoot,
    marker authority.snapshot.domain profile.semantics command⟩

def patchOf {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {directory : LoadedDirectory durable}
    {authority : Loaded deployment durable.snapshot}
    {pay : PayCellDomain.Loaded deployment durable.snapshot}
    {book : BookCell deployment directory.directory} {tariff : Tariff} {price : Price}
    (command : Command) {decision : Decision}
    (legs : Legs deployment profile ambient directory authority pay book tariff price decision) :
    Patch PayCell.layout :=
  payPatch command.observation decision legs.account legs.record ++
    PayChainTip.patch (chainTipOf pay.cell.logical) command.tip

/-- The price the decision is made at, on the loaded authority cell. -/
abbrev priceAt (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) {durable : Durable} (authority : Loaded deployment durable.snapshot)
    (command : Command) : Price :=
  priceIn deployment profile.semantics profile.template ambient authority.snapshot command.observation

structure Prepared (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) (verified : Verified) where
  private mk ::
  directory : LoadedDirectory durable
  authority : Loaded deployment durable.snapshot
  pay : PayCellDomain.Loaded deployment durable.snapshot
  book : BookCell deployment directory.directory
  factory : FactoryCell deployment directory.directory
  tariff : Tariff
  tariffExact : tariffOf pay.cell.logical = some tariff
  clock : ClockCellDomain.Loaded deployment durable.snapshot
  tipAhead : clock.clock.slot ≤ command.tip.slot
  chainTipAhead : PayChainTip.advances (chainTipOf pay.cell.logical) command.tip
  clockValid : ValidatedPatch ClockCell.materializer clock.cell clock.cell.root
    (ClockCell.tickPatch clock.clock (PayObservation.advanceClock clock.clock command.tip))
  decision : Decision
  decided : decideEnrol pay.cell.logical (priceAt deployment profile ambient authority command)
    command.tip command.observation verified (subjectTakenIn authority.snapshot command.observation) =
      .ok decision
  legs : Legs deployment profile ambient directory authority pay book tariff
    (priceAt deployment profile ambient authority command) decision
  candidate : Candidate (family deployment authority.snapshot pay.cell profile.semantics ambient command
      (patchOf command legs))
    pay.cell (declarationOf command legs) ()
  source : CanonicalCellRegistry.LoadedPolicySource authority.snapshot.domain directory.directory
    (authority.snapshot.authState.policyAddress ⟨deployment.factoryId⟩
      (authority.snapshot.authState.policyRevision ⟨deployment.factoryId⟩))
  dependencies : WorldKindLawDependencies.Dependencies
  dependenciesExact : WorldKindLawDependencies.loadTarget deployment directory.directory
    deployment.factoryId = some dependencies
  lawGuards : List (Nat × Digest)
  lawGuardsExact : PhysicalLawResolution.readGuards authority.snapshot directory.directory
    profile.semantics deployment.factoryId dependencies.additional = some lawGuards

/-- The whole preparation, in order: the loaded cells, the two pinned roots,
the clock, the pure decision (`decideEnrol`, at the birth fee of the key the
memo names and the authority cell's answer for its subject), the decision's
legs, the pay patch, and the factory law's source.  No step installs anything. -/
def prepare (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) (verified : Verified) :
    Except Reject (Prepared deployment profile ambient durable command verified) := do
  let directory ← requireSome .directoryUnavailable (loadDirectory durable)
  let authority ← requireSome .authorityUnavailable (loadDeployment deployment durable.snapshot)
  let pay ← requireSome .payUnavailable (PayCellDomain.load deployment durable.snapshot)
  let clock ← requireSome .clockUnavailable (ClockCellDomain.load deployment durable.snapshot)
  let book ← requireSome .bookUnavailable
    (ResourceBirthController.Concrete.observeCell deployment directory.directory
      deployment.resourceBookId .resourceBook)
  let factory ← requireSome .factoryUnavailable
    (ResourceBirthController.Concrete.observeCell deployment directory.directory
      deployment.factoryId .declaredObject)
  let snapshot := authority.snapshot
  if command.expectedAuthorityRoot = snapshot.cell.root then
    if rootExact : command.expectedPayRoot = pay.cell.root then
      match tariffExact : tariffOf pay.cell.logical with
      | none => throw (.decision .tariffInvalid)
      | some tariff =>
        if tipAhead : clock.clock.slot ≤ command.tip.slot then
          if chainTipAhead : PayChainTip.advances (chainTipOf pay.cell.logical) command.tip then
            match validate ClockCell.materializer clock.cell clock.cell.root
                (ClockCell.tickPatch clock.clock (PayObservation.advanceClock clock.clock command.tip)) with
            | .rejected _ => throw .validation
            | .accepted clockValid =>
            match decided : decideEnrol pay.cell.logical (priceAt deployment profile ambient authority command)
                command.tip command.observation verified
                (subjectTakenIn authority.snapshot command.observation) with
            | .error reason => throw (.decision reason)
            | .ok decision =>
              let legs ← prepareLegs deployment profile ambient directory authority pay book tariff
                (priceAt deployment profile ambient authority command) decision
              match validate PayCell.materializer pay.cell pay.cell.root
                  (patchOf command legs) with
              | .rejected _ => throw .validation
              | .accepted validated =>
                  let source ← requireSome .policyUnavailable (CanonicalCellRegistry.loadPolicySource
                    snapshot.domain directory.directory
                    (snapshot.authState.policyAddress ⟨deployment.factoryId⟩
                      (snapshot.authState.policyRevision ⟨deployment.factoryId⟩)))
                  let candidate : Candidate (family deployment snapshot pay.cell profile.semantics
                      ambient command (patchOf command legs)) pay.cell
                      (declarationOf command legs) () :=
                    { preStateBound := rfl
                      modeEvidence := ⟨rootExact⟩
                      validated := validated
                      postcondition := validated.resultAt }
                  match dependenciesExact : WorldKindLawDependencies.loadTarget deployment
                      directory.directory deployment.factoryId with
                  | none => throw .policyUnavailable
                  | some dependencies =>
                    match lawGuardsExact : PhysicalLawResolution.readGuards snapshot directory.directory
                        profile.semantics deployment.factoryId dependencies.additional with
                    | none => throw .policyUnavailable
                    | some lawGuards =>
                      pure ⟨directory, authority, pay, book, factory, tariff, tariffExact, clock,
                        tipAhead, chainTipAhead, clockValid, decision, decided, legs, candidate, source,
                        dependencies, dependenciesExact, lawGuards, lawGuardsExact⟩
          else throw .chainTipRegressed
        else throw .tipBehindClock
    else throw .stalePay
  else throw .staleAuthority

variable {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
  {ambient : Ambient} {durable : Durable} {command : Command} {verified : Verified}

def Prepared.payPost (prepared : Prepared deployment profile ambient durable command verified) :
    PayCell.Cell :=
  prepared.candidate.validated.apply

def Prepared.declaration (prepared : Prepared deployment profile ambient durable command verified) :
    Declaration :=
  declarationOf command prepared.legs

def project (prepared : Prepared deployment profile ambient durable command verified)
    (_logical : PayStore) : Minidregg.Pred.State :=
  ⟨WorldKindLawDependencies.targetSelectorSlots prepared.directory.directory deployment.factoryId ++
    CanonicalRuntimeProfile.requestSlots
      (request deployment prepared.authority.snapshot prepared.pay.cell profile.semantics ambient
        command prepared.declaration) ++
    [(NativeHostGenesis.selfEnrolSlot, 1),
     ("pay/decision", Int.ofNat (decisionTag prepared.decision)),
     ("pay/amount", Int.ofNat command.observation.amount),
     ("pay/price", Int.ofNat (enrolPrice prepared.tariff
        (priceAt deployment profile ambient prepared.authority command)))] ++
    ResourceAuthorityProjection.grantSlots "authority/enrol" .program command.capability
      prepared.authority.snapshot.logical⟩

def step (prepared : Prepared deployment profile ambient durable command verified) :
    PolicyStepContext :=
  PolicyStepContext.ofCandidate (project prepared) profile.semantics prepared.candidate

def sourceStore (prepared : Prepared deployment profile ambient durable command verified) :
    CanonicalPolicyRegistry.PayloadStore :=
  ⟨CanonicalCellRegistry.fetchPolicySource prepared.authority.snapshot.domain
    prepared.directory.directory⟩

/-- The factory is the request's actual target. Preparation retains the exact
structural dependencies and complete current/pinned law-source read set. -/
def policyConfig [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command verified) :
    ComposedPolicyAdmission.Config F :=
  PhysicalLawResolution.config profile.compilerProfile prepared.authority.snapshot
    prepared.directory.directory
    (sourceCapabilityPortal prepared.authority.snapshot
      (marker prepared.authority.snapshot.domain profile.semantics command))
    (step prepared) deployment.factoryId prepared.dependencies.additional

def lawReadGuards (prepared : Prepared deployment profile ambient durable command verified) :
    List (Nat × Digest) := prepared.lawGuards ++ prepared.dependencies.readGuards

/-- No absent resolver can be interpreted as an empty dependency list. -/
theorem Prepared.complete_law_dependencies
    (prepared : Prepared deployment profile ambient durable command verified) :
    WorldKindLawDependencies.loadTarget deployment prepared.directory.directory deployment.factoryId =
      some prepared.dependencies ∧
    PhysicalLawResolution.readGuards prepared.authority.snapshot prepared.directory.directory
      profile.semantics deployment.factoryId prepared.dependencies.additional = some prepared.lawGuards :=
  ⟨prepared.dependenciesExact, prepared.lawGuardsExact⟩

abbrev Prepared.SemanticAccepted [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command verified) :=
  AcceptedCellEffect (portal := (policyConfig prepared).portal)
    (authState := prepared.authority.snapshot.authState)
    (family deployment prepared.authority.snapshot prepared.pay.cell profile.semantics ambient command
      (patchOf command prepared.legs))
    (request deployment prepared.authority.snapshot prepared.pay.cell profile.semantics ambient
      command prepared.declaration)
    prepared.pay.cell prepared.declaration ()

/-- The observer's request under the factory's CURRENT law: capability mode
with `C_enrol`, the slot `authority/operation/pay-self-enrol = 1`. -/
def authorize [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command verified)
    (receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot) :
    Except Reject prepared.SemanticAccepted := do
  let wanted := request deployment prepared.authority.snapshot prepared.pay.cell profile.semantics
    ambient command prepared.declaration
  let config := policyConfig prepared
  let evidence ← requireSome .capabilityRejected
    (config.capabilityEvidenceChecked wanted command.capability () receipt () (fun _ => ())).toOption
  let law ← requireSome .policyUnavailable config.resolve?
  let witness := law.witness
  if inputsInRange profile.compilerProfile.compiler law.predicate
      (step prepared).oldState (step prepared).newState != true then
    throw .policyInputRange
  if !decide (castInjOn F
      (intsOf law.predicate (step prepared).oldState (step prepared).newState)) then
    throw .policyCastAlias
  match ComposedPolicyAdmission.admit config wanted
      evidence witness (.policy wanted.policyId wanted.policyRevision) rfl rfl with
  | none => .error .policyRejected
  | some authorization =>
      .ok (prepared.candidate.accept authorization rfl rfl rfl .sealed trivial)

structure Accepted [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command verified)
    (ingress : DecodedIngress) where
  private mk ::
  receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot
  envelopeExact : receipt.envelopeBytes = ingress.ingress.envelope
  semantic : prepared.SemanticAccepted

/-- An accepted observer submission satisfies the resolved current law, including
inherited/ambient/kind components, on this exact source-prepared effect. -/
theorem Accepted.composed_law_evaluated [DecidableEq F]
    {prepared : Prepared deployment profile ambient durable command verified}
    {ingress : DecodedIngress} (accepted : Accepted prepared ingress) :
    ∃ graph : PolicyComponentResolution.LoadedGraph
        (policyConfig prepared).snapshot (policyConfig prepared).store
        (policyConfig prepared).profile.semantics (policyConfig prepared).target
        (policyConfig prepared).additional,
      PolicyComponentResolution.loadTarget (policyConfig prepared).snapshot
        (policyConfig prepared).store (policyConfig prepared).profile.semantics
        (policyConfig prepared).target (policyConfig prepared).resolutionBudget
        (policyConfig prepared).additional = .ok graph ∧
      Minidregg.Pred.eval (ResolvedLawCompilation.predicate graph.resolved)
        (step prepared).oldState (step prepared).newState = true := by
  exact ComposedPolicyAdmission.authorized_effective_law (policyConfig prepared)
    (request deployment prepared.authority.snapshot prepared.pay.cell profile.semantics
      ambient command prepared.declaration) accepted.semantic.authorization

def admitNative [DecidableEq F] (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared deployment profile ambient durable command verified)
    (ingress : DecodedIngress) : IO (Except Reject (Accepted prepared ingress)) := do
  match ← CredentialSignatureAdmission.verifyNative native prepared.authority.snapshot
      (marker prepared.authority.snapshot.domain profile.semantics command)
      (request deployment prepared.authority.snapshot prepared.pay.cell profile.semantics ambient
        command prepared.declaration)
      ingress.ingress.envelope with
  | .error reason => return .error (.signature reason)
  | .ok receipt =>
      if same : receipt.envelopeBytes = ingress.ingress.envelope then
        match authorize prepared receipt with
        | .error reason => return .error reason
        | .ok semantic => return .ok ⟨receipt, same, semantic⟩
      else return .error .capabilityRejected

/-! ## The physical intent -/

def payWrite (prepared : Prepared deployment profile ambient durable command verified) : DataWrite :=
  prepared.pay.write prepared.payPost

/-- The clock cell after the payment: `PayObservation.advanceClock` at the tip. -/
def Prepared.clockPost (prepared : Prepared deployment profile ambient durable command verified) :
    ClockCell.Cell :=
  prepared.clockValid.apply

def clockWrite (prepared : Prepared deployment profile ambient durable command verified) : DataWrite :=
  prepared.clock.write prepared.clockPost

/-- The pay cell, the clock cell, then the decision's other cells. -/
def writes (prepared : Prepared deployment profile ambient durable command verified) :
    List DataWrite :=
  payWrite prepared :: clockWrite prepared :: prepared.legs.writes prepared.factory

def policyGuard (prepared : Prepared deployment profile ambient durable command verified) :
    ReadGuard :=
  ⟨⟨prepared.source.readGuard.1⟩, prepared.source.readGuard.2⟩

def readGuards (prepared : Prepared deployment profile ambient durable command verified) :
    List ReadGuard :=
  policyGuard prepared ::
    (prepared.authority.readGuards ++
      (lawReadGuards prepared).map (fun (cellIdentifier, expectedRoot) => (⟨⟨cellIdentifier⟩, expectedRoot⟩ : ReadGuard))).filter fun guard =>
      guard.cellId ∉ (writes prepared).map DataWrite.cellId

def PhysicalShape (prepared : Prepared deployment profile ambient durable command verified) : Prop :=
  ((writes prepared).map DataWrite.cellId).Nodup ∧
    (∀ write ∈ writes prepared, write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
    (∀ write ∈ writes prepared, ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
    (∀ write ∈ writes prepared, rootBytes write.canonicalPostBytes = write.exactPost) ∧
    (policyGuard prepared).cellId ∉ (writes prepared).map DataWrite.cellId ∧
    (∀ guard ∈ readGuards prepared, guard.expectedRoot = durable.snapshot.model.roots guard.cellId)

instance physicalShapeDecidable
    (prepared : Prepared deployment profile ambient durable command verified) :
    Decidable (PhysicalShape prepared) := by
  unfold PhysicalShape
  infer_instance

theorem readGuards_readonly (prepared : Prepared deployment profile ambient durable command verified)
    (shape : PhysicalShape prepared) (guard : ReadGuard) (member : guard ∈ readGuards prepared) :
    guard.cellId ∉ (writes prepared).map DataWrite.cellId := by
  rcases List.mem_cons.mp member with rfl | authority
  · exact shape.2.2.2.2.1
  · simpa using (List.mem_filter.mp authority).2

def nullifiers (prepared : Prepared deployment profile ambient durable command verified) :
    List StableNullifier :=
  [nullifier deployment.domain command.observation, tickNullifier deployment.domain command.tip] ++
    prepared.legs.nullifiers

end Preparation

/-! ## The verifier's bits -/

/-- The two possession bits for the observation's memo, from the pinned
native verifier over the tariff's mint and the observed enrollment address.
An unparsed memo needs no verification (`false, false`; the decision journals
it by its memo reason before reading the bits).  A native failure is a
refusal. -/
def verifyFor (native : CredentialSignatureIO.NativeConfig) (deployment : Deployment)
    (durable : Durable) (o : Observation) : IO (Except Reject Verified) := do
  match parsedMemo o with
  | none => return .ok ⟨false, false⟩
  | some memo =>
      let mint := ((PayCellDomain.load deployment durable.snapshot).bind
        (fun pay => tariffOf pay.cell.logical)).map Tariff.mint
      match mint with
      | none => return .error .payUnavailable
      | some mint =>
          match ← PayEnrolSignatureIO.verifyNative native mint o.address memo with
          | .error error => return .error (.verifier error)
          | .ok checked => return .ok checked.verified

/-! ## The receiver -/

section Receiver

variable {F : Type} [Field F] [DecidableEq F]

structure AcceptedEnrol (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (ingress : DecodedIngress) where
  private mk ::
  verified : Verified
  prepared : Prepared deployment profile ambient durable ingress.command verified
  accepted : PayEnrolReceiver.Accepted prepared ingress
  physical : PhysicalShape prepared

def admitDecodedNative (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (native : CredentialSignatureIO.NativeConfig)
    (ingress : DecodedIngress) :
    IO (Except Reject (AcceptedEnrol deployment profile ambient durable ingress)) := do
  match ← verifyFor native deployment durable ingress.command.observation with
  | .error reason => return .error reason
  | .ok verified =>
    match prepare deployment profile ambient durable ingress.command verified with
    | .error reason => return .error reason
    | .ok prepared =>
      if physical : PhysicalShape prepared then
        match ← admitNative native prepared ingress with
        | .error reason => return .error reason
        | .ok accepted => return .ok ⟨verified, prepared, accepted, physical⟩
      else return .error .physicalPreparation

variable {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
  {ambient : Ambient} {durable : Durable} {ingress : DecodedIngress}

def transactionId (domain semantics : Digest) (ingress : DecodedIngress) : Digest :=
  ⟨marker domain semantics ingress.command⟩

def event (domain : Digest) (ingress : DecodedIngress) : StableEvent where
  codecVersion := 1
  domain := domain
  eventId := (Sp800185Cshake256.hash "DREGG.PAY.SELF-ENROL.EVENT/v1".toUTF8.toList
    ingress.bytes).digest
  canonicalBytes := ingress.bytes

def charge (accepted : AcceptedEnrol deployment profile ambient durable ingress) :
    ResourceCost.Charge
  | .incidences => (writes accepted.prepared).length
  | .turnBytes => ingress.bytes.length
  | .memoryTouches => (writes accepted.prepared).length + (readGuards accepted.prepared).length
  | .storageBytes => ((writes accepted.prepared).map fun write => write.canonicalPostBytes.length).sum
  | .witnessBytes => ingress.ingress.envelope.length
  | .proofWork => 2
  | .feeDebit | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

def intent (accepted : AcceptedEnrol deployment profile ambient durable ingress) :
    DataIntent rootBytes where
  transactionId := transactionId deployment.domain profile.semantics ingress
  subject := some ingress.command.observer
  writes := writes accepted.prepared
  readGuards := readGuards accepted.prepared
  nullifiers := nullifiers accepted.prepared
  exactCharge := charge accepted
  event := event deployment.domain ingress
  postRootsBound := accepted.physical.2.2.2.1
  guardsReadOnly := readGuards_readonly accepted.prepared accepted.physical

structure Receipt where
  transactionId : Digest
  eventId : Digest
  deriving DecidableEq, Repr

def receipt (domain semantics : Digest) (ingress : DecodedIngress) : Receipt :=
  ⟨transactionId domain semantics ingress, (event domain ingress).eventId⟩

/-- A recorded submission of the same ingress: same transaction, same event,
and its first two nullifiers are this observation's transfer and tick. -/
def replay (domain semantics : Digest) (durable : Durable) (ingress : DecodedIngress) :
    Option (Except Unit Receipt) :=
  match DurableCommitProtocol.Snapshot.lookupRecorded
      (transactionId domain semantics ingress) durable.snapshot.model.journal with
  | none => none
  | some recorded =>
    if recorded.transactionId = transactionId domain semantics ingress ∧
        recorded.event.event = event domain ingress ∧
        recorded.nullifiers.take 2 =
          [nullifier domain ingress.command.observation, tickNullifier domain ingress.command.tip] then
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
      | .confirmed kind _ =>
          return .confirmed kind (receipt deployment.domain profile.semantics ingress)
      | .rejected reason => return .durableRejected reason
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

end Receiver

/-! ## The signing header -/

/-- The exact header the observer signs: the request the receiver will
rebuild, over the decision it will reach.  When preparation refuses, the
header is built over an empty declaration (submission then refuses with the
named reason); a signer key the authority cell does not hold is refused. -/
def signingHeader {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (native : CredentialSignatureIO.NativeConfig) (command : Command) :
    IO (Except String CredentialSignedEnvelopeController.SignedHeader) := do
  let some authority := loadDeployment deployment durable.snapshot
    | return .error "authority unavailable"
  let some pay := PayCellDomain.load deployment durable.snapshot
    | return .error "pay cell unavailable"
  let declaration : Declaration ←
    match ← verifyFor native deployment durable command.observation with
    | .error _ => pure ⟨[], [], command.expectedPayRoot, marker deployment.domain profile.semantics command⟩
    | .ok verified =>
      match prepare deployment profile ambient durable command verified with
      | .ok prepared => pure prepared.declaration
      | .error _ => pure ⟨[], [], command.expectedPayRoot, marker deployment.domain profile.semantics command⟩
  return (CredentialSignatureAdmission.signingHeader authority.snapshot
    (marker deployment.domain profile.semantics command)
    ⟨.program, request deployment authority.snapshot pay.cell profile.semantics ambient command
      declaration⟩).mapError
      (fun reason => s!"pay-enrol signer key: {repr reason}")

end Minidregg.Kernel.PayEnrolReceiver
