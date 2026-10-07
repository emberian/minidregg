/-
# Kernel.PayEnrolReceiver — one enrollment-index payment is one turn (PAY §11.4, P3b-2)

The observer submits one finalized transfer to the enrollment index
(`Tariff.enrolIndex`) as a signed `Command`.  The family (`payEnrolFamily`, a
`Kernel.Receiving.Family`) makes ONE claim -- the observer's current key over the
envelope's signed header -- and OBSERVES the memo's two possession signatures
(`observations`: Ed25519 by the Mini key over `miniFrame`, `SSHSIG` by the ssh
key under `dregg-enrol@v1`).  The Receiver's verifier answers all three before
`prepare`; a verifier error refuses, a `false` possession bit journals the
payment (`miniSigInvalid`, …).  `prepare` decides with
`PayEnrolDecision.decideEnrol` on those answers (`verifiedOf`;
`committed_verified`), plans ONE durable intent, builds the capability receipt
from the Receiver's voucher and binds the request to the factory's committed
head.  It judges no law: the Receiver judges every written cell
(`committed_lawful`, `committed_admitted`).

* **enrol** — writes the authority cell, the factory, the Book, the new
  account's cell, the new account law's source cell and the pay cell:
  - authority: the Mini key as a new subject `subjectOf miniKey`
    (`keyEntries`), the account's two owner grants and initial law (an
    ordinary resource birth's grant batch, `ResourceBirthAuthority.entries`),
    and one factory-observation grant (`observeObject` on the factory, the M3
    provisioning grant);
  - the account birth through the resource-birth controller's own preparation
    (`allocate?`, `BirthsAdmissible`, `TemplateBound`, `PhysicalPostLaw`): a
    declared account owned by the new subject, judged by its export law, and its
    law source, born under the same export law (`kernelOnlyOrBorn`);
  - Book: `mint credit` to the enrollment float, the lease (`weeks · nodeWeekRate`)
    and the birth fee to the tariff's collector, the remainder to the new
    account — the float ends where it started;
  - pay cell: `enrolment[miniKey]`, `sshIndex[blob]`,
    `assignment[nextFree] := account`;
  - clock cell: `slot := tip.slot`, `now` to the tip's block time when later
    (`PayObservation.advanceClock`), as an observation report does.
* **renew** — writes the Book (mint to the float, the lease to the collector,
  the remainder to the friend's account), the pay cell (the enrolment row's
  `leaseUntil`), the clock cell and the factory at its loaded payload.
* **journal** — writes the pay cell (`journal[nullifier]`), the clock cell and
  the factory at its loaded payload.  Nothing is minted.

Every branch writes the factory, so the factory's law judges every
enrollment-index payment (the observer's `installPolicy` request, presenting
`C_enrol`, with `authority/operation/pay-self-enrol = 1`,
`NativeHostGenesis.confinedFactoryLaw`); the pay cell's law admits the same
request by its self-enrollment clause.  Every branch spends the transfer's
nullifier `soltx:‖sig‖addr` and the tip's tick nullifier; the enrol branch also
spends the birth identity's authority marker (`Family.spent`).

One intent writing several cells is the existing mechanism: a `DataIntent`'s
writes are a list over cells and `DurableDataIntent.execute` installs all of
them or none (`PayEnrolProofs.multi_cell_intent_atomic`).
-/
import Kernel.ClockCellDomain
import Kernel.PayObservationReceiver
import Kernel.PayChainTip
import Kernel.PayEnrolDecision
import Kernel.ParticipantKeyEnrollment
import Kernel.NativeHostGenesis
import Kernel.ClockLaw

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
open Minidregg.Theory.Receiving (SigQuery Vouchers)

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
def leaseCost (tariff : Tariff) (weeks : Nat) : Nat := weeks * tariff.nodeWeekRate

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
        descriptor.resourceBatch.operations, []⟩

def renewBatch (tariff : Tariff) (collector : Nat) (plan : RenewPlan) :
    CanonicalResourceKernel.Batch :=
  ⟨[], [.mint tariff.asset plan.float plan.credit,
    .fee plan.float collector tariff.asset (leaseCost tariff plan.weeks),
    .transfer plan.float plan.account tariff.asset (renewRemainder tariff plan)], []⟩

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
  | directoryUnavailable | authorityUnavailable | payUnavailable
  | bookUnavailable | factoryUnavailable | staleAuthority | stalePay
  | clockUnavailable | tipBehindClock | chainTipRegressed
  | decision (reason : PayEnrolDecision.Reject)
  /-- The Receiver did not answer one of the memo's observed signatures (it always
  does: `admitVia` answers every observation or refuses `.verifier`). -/
  | unobserved
  | grantBatch | birthShape | keyTaken | observeGrantTaken | authorityEntries
  | allocation | bookAdmission | renewalRecord
  | validation
  | policyUnavailable | capabilityRejected | policyRejected
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

/-- The cells each decision writes besides the pay and clock cells.  Every
branch writes the factory at its loaded payload (an enrollment's through the
birth plan), so the factory's law judges every enrollment-index payment. -/
def Legs.writes (factory : FactoryCell deployment directory.directory) : {decision : Decision} →
    Legs deployment profile ambient directory authority pay book tariff price decision →
      List DataWrite
  | _, .enrol _ legs =>
      ResourceBirthController.Concrete.planWrites deployment legs.descriptor factory.payload
        book.payload legs.resources.post (authority.writes legs.authorityPost)
  | _, .renew _ _ _ resources =>
      [ResourceBirthController.Concrete.packedWrite deployment.factoryId
        ⟨.declaredObject, factory.payload⟩ ⟨.declaredObject, factory.payload⟩,
       ResourceBirthController.Concrete.packedWrite deployment.resourceBookId
        ⟨.resourceBook, book.payload⟩ ⟨.resourceBook, resources.post⟩]
  | _, .journal _ =>
      [ResourceBirthController.Concrete.packedWrite deployment.factoryId
        ⟨.declaredObject, factory.payload⟩ ⟨.declaredObject, factory.payload⟩]

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

variable {F : Type} [Field F] [DecidableEq F]

/-- The clock write's law step (`ClockLaw.step`): the clock target's selector
slots, the observer's signed self-enrollment request, operation
`pay-self-enrol`, and the clock before and after the validated advance. -/
def clockStepOf (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (command : Command) (directory : Directory Nat Registry)
    (snapshot : Snapshot) (pay : PayCell.Cell) (clock : ClockCell.Cell) (current : ClockCell.Clock)
    (d : Declaration) {patch : Patch ClockCell.layout}
    (clockValid : ValidatedPatch ClockCell.materializer clock clock.root patch) : PolicyStepContext :=
  ClockLaw.step (WorldKindLawDependencies.targetSelectorSlots directory
      (ClockCell.physicalId deployment.domain))
    (request deployment snapshot pay profile.semantics ambient command d)
    ClockLaw.paySelfEnrolSlot current profile.semantics
    (effectDigest snapshot.domain profile.semantics command d) clockValid

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

/-- **The enrollment, decided and planned before any authorization**: the loaded
cells, the two pinned roots, the clock advance, the pure decision (`decideEnrol`,
at the birth fee of the key the memo names, the authority cell's answer for its
subject, and the Receiver's answers on the memo's two signatures), the decision's
legs, the pay patch, and the factory law's dependencies.  No law is judged here:
the Receiver judges every written cell. -/
structure Planned (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) (verified : Verified) where
  private mk ::
  directory : LoadedDirectory durable
  directoryExact : loadDirectory durable = some directory
  authority : Loaded deployment durable.snapshot
  authorityExact : loadDeployment deployment durable.snapshot = some authority
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
  dependencies : WorldKindLawDependencies.Dependencies
  dependenciesExact : WorldKindLawDependencies.loadTarget deployment directory.directory
    deployment.factoryId = some dependencies

/-- **What every `Planned` enrollment means** (layer 1): the observer read the
loaded authority and pay roots, the decision is `decideEnrol`'s on the loaded pay
cell under exactly `verified`, the clock advance is the tip's, and the factory
law's structural dependencies are the loaded ones. -/
theorem Planned.sound {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {command : Command} {verified : Verified}
    (planned : Planned deployment profile ambient durable command verified) :
    decideEnrol planned.pay.cell.logical (priceAt deployment profile ambient planned.authority command)
        command.tip command.observation verified
        (subjectTakenIn planned.authority.snapshot command.observation) = .ok planned.decision ∧
      planned.clock.clock.slot ≤ command.tip.slot ∧
      PayChainTip.advances (chainTipOf planned.pay.cell.logical) command.tip ∧
      WorldKindLawDependencies.loadTarget deployment planned.directory.directory
        deployment.factoryId = some planned.dependencies :=
  ⟨planned.decided, planned.tipAhead, planned.chainTipAhead, planned.dependenciesExact⟩

/-- Plan the enrollment under the verifier's answers `verified`. -/
def plan (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) (verified : Verified) :
    Except Reject (Planned deployment profile ambient durable command verified) := do
  match directoryExact : loadDirectory durable with
  | none => throw .directoryUnavailable
  | some directory =>
  match authorityExact : loadDeployment deployment durable.snapshot with
  | none => throw .authorityUnavailable
  | some authority =>
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
                  pure ⟨directory, directoryExact, authority, authorityExact, pay, book, factory, tariff, tariffExact, clock,
                    tipAhead, chainTipAhead, clockValid, decision, decided, legs, candidate,
                    dependencies, dependenciesExact⟩
          else throw .chainTipRegressed
        else throw .tipBehindClock
    else throw .stalePay
  else throw .staleAuthority

variable {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
  {ambient : Ambient} {durable : Durable} {command : Command} {verified : Verified}

def Planned.payPost (planned : Planned deployment profile ambient durable command verified) :
    PayCell.Cell :=
  planned.candidate.validated.apply

def Planned.declaration (planned : Planned deployment profile ambient durable command verified) :
    Declaration :=
  declarationOf command planned.legs

def project (planned : Planned deployment profile ambient durable command verified)
    (_logical : PayStore) : Minidregg.Pred.State :=
  ⟨WorldKindLawDependencies.targetSelectorSlots planned.directory.directory deployment.factoryId ++
    CanonicalRuntimeProfile.requestSlots
      (request deployment planned.authority.snapshot planned.pay.cell profile.semantics ambient
        command planned.declaration) ++
    [(ClockLaw.paySelfEnrolSlot, 1),
     ("pay/decision", Int.ofNat (decisionTag planned.decision)),
     ("pay/amount", Int.ofNat command.observation.amount),
     ("pay/price", Int.ofNat (enrolPrice planned.tariff
        (priceAt deployment profile ambient planned.authority command)))] ++
    ResourceAuthorityProjection.grantSlots "authority/enrol" .program command.capability
      planned.authority.snapshot.logical⟩

/-- The enrollment's law step: the factory's selector slots, the observer's
self-enrollment request (`installPolicy` on the factory, the self-enrol slot 1),
the decision, the amount and the price.  The factory's law, the pay cell's law
and a newborn's export law all judge this step. -/
def step (planned : Planned deployment profile ambient durable command verified) :
    PolicyStepContext :=
  PolicyStepContext.ofCandidate (project planned) profile.semantics planned.candidate

/-- The factory is the request's actual target.  The configuration binding
reads the factory's committed law at its loaded head. -/
def policyConfig
    (planned : Planned deployment profile ambient durable command verified) :
    ComposedPolicyAdmission.Config F :=
  PhysicalLawResolution.config profile.compilerProfile planned.authority.snapshot
    planned.directory.directory
    (sourceCapabilityPortal planned.authority.snapshot
      (marker planned.authority.snapshot.domain profile.semantics command))
    (step planned) deployment.factoryId planned.dependencies.additional

/-- The clock write's law step. -/
def Planned.clockStep (planned : Planned deployment profile ambient durable command verified) :
    PolicyStepContext :=
  clockStepOf deployment profile ambient command planned.directory.directory
    planned.authority.snapshot planned.pay.cell planned.clock.cell planned.clock.clock
    planned.declaration planned.clockValid

end Preparation

/-! ## The patch -/

section Patch

variable {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {command : Command} {verified : Verified}

def payWrite (planned : Planned deployment profile ambient durable command verified) : DataWrite :=
  planned.pay.write planned.payPost

def clockWrite (planned : Planned deployment profile ambient durable command verified) : DataWrite :=
  planned.clock.write planned.clockValid.apply

/-- The pay cell, the clock cell, then the decision's other cells (an
enrollment's newborn account and law source, the factory, the Book and the
authority cell; a renewal's Book). -/
def writes (planned : Planned deployment profile ambient durable command verified) :
    List DataWrite :=
  payWrite planned :: clockWrite planned :: planned.legs.writes planned.factory

/-- **The family projects; the Receiver judges.**  A write's step is chosen by
the kind its post holds: the clock carries the clock law's step; a kernel-only
cell (the authority cell, the Book) none; every other write -- the pay cell, the
factory, an enrollment's newborns -- the enrollment step, which the pay law, the
factory's law and the newborns' export law each judge. -/
def lawStepOf (planned : Planned deployment profile ambient durable command verified)
    (write : DataWrite) : Option PolicyStepContext :=
  match ReceivingLaw.livePost write with
  | some ⟨.clock, _⟩ => some planned.clockStep
  | some ⟨kind, _⟩ =>
      match kind.lawClass with
      | .kernelOnly _ => none
      | _ => some (step planned)
  | none => some (step planned)

theorem lawStepOf_pay (planned : Planned deployment profile ambient durable command verified) :
    lawStepOf planned (payWrite planned) = some (step planned) := by
  unfold lawStepOf
  rw [ReceivingLaw.livePost_live (cell := PayCellDomain.packedCell planned.payPost) rfl]
  rfl

theorem lawStepOf_clock (planned : Planned deployment profile ambient durable command verified) :
    lawStepOf planned (clockWrite planned) = some planned.clockStep := by
  unfold lawStepOf
  rw [ReceivingLaw.livePost_live (cell := ClockCellDomain.packedCell planned.clockValid.apply) rfl]
  rfl

/-- Every write of an enrollment's legs is bound: its exact post is its post
bytes' root (each is a birth write, a packed write or the authority write). -/
theorem Legs.writes_bound {directory : LoadedDirectory durable}
    {authority : Loaded deployment durable.snapshot}
    {pay : PayCellDomain.Loaded deployment durable.snapshot}
    {book : BookCell deployment directory.directory} {tariff : Tariff} {price : Price}
    (factory : FactoryCell deployment directory.directory) :
    {decision : Decision} →
    (legs : Legs deployment profile ambient directory authority pay book tariff price decision) →
    ∀ write ∈ legs.writes factory, rootBytes write.canonicalPostBytes = write.exactPost
  | _, .enrol _ legs, write, member => by
      simp only [Legs.writes, ResourceBirthController.Concrete.planWrites,
        ResourceBirthController.allocationWrites, CredentialAuthorityDomainReceiver.Loaded.writes,
        List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at member
      rcases member with ((⟨request, -, rfl⟩ | rfl | rfl) | rfl) <;> rfl
  | _, .renew _ _ _ _, write, member => by
      simp only [Legs.writes, List.mem_cons, List.mem_nil_iff, or_false] at member
      rcases member with rfl | rfl <;> rfl
  | _, .journal _, write, member => by
      simp only [Legs.writes, List.mem_cons, List.mem_nil_iff, or_false] at member
      subst member; rfl

/-- Every branch writes the factory at its loaded payload. -/
theorem Legs.factory_mem {directory : LoadedDirectory durable}
    {authority : Loaded deployment durable.snapshot}
    {pay : PayCellDomain.Loaded deployment durable.snapshot}
    {book : BookCell deployment directory.directory} {tariff : Tariff} {price : Price}
    (factory : FactoryCell deployment directory.directory) :
    {decision : Decision} →
    (legs : Legs deployment profile ambient directory authority pay book tariff price decision) →
    ResourceBirthController.Concrete.packedWrite deployment.factoryId
        ⟨.declaredObject, factory.payload⟩ ⟨.declaredObject, factory.payload⟩ ∈ legs.writes factory
  | _, .enrol _ _ => by simp [Legs.writes, ResourceBirthController.Concrete.planWrites]
  | _, .renew _ _ _ _ => by simp [Legs.writes]
  | _, .journal _ => by simp [Legs.writes]

theorem writes_bound (planned : Planned deployment profile ambient durable command verified)
    (write : DataWrite) (member : write ∈ writes planned) :
    rootBytes write.canonicalPostBytes = write.exactPost := by
  simp only [writes, List.mem_cons] at member
  rcases member with rfl | rfl | legs
  · rfl
  · rfl
  · exact Legs.writes_bound planned.factory planned.legs write legs

def physicalPostLaw (planned : Planned deployment profile ambient durable command verified) : Bool :=
  (writes planned).all fun write =>
    decide (ResourceBirthController.Concrete.PhysicalPostLaw deployment write)

end Patch

/-! ## The signatures: one claim, two observations -/

section Signatures

/-- The tariff's mint, read from the loaded pay cell. -/
def mintOf (deployment : Deployment) (durable : Durable) : Option Address32 :=
  ((PayCellDomain.load deployment durable.snapshot).bind fun pay => tariffOf pay.cell.logical).map
    Tariff.mint

/-- The memo's Mini-key possession query: Ed25519 over `miniFrame`. -/
def miniQuery (mint enrolAddress : Address32) (memo : Memo) : SigQuery :=
  ⟨.ed25519, memo.miniKey, miniFrame mint enrolAddress memo, memo.miniSig⟩

/-- The memo's ssh-key possession query: `SSHSIG` under `dregg-enrol@v1` over
`sshsigMessage`. -/
def sshQuery (mint enrolAddress : Address32) (memo : Memo) : SigQuery :=
  ⟨.sshsig sshsigNamespace, memo.sshKey, sshsigMessage mint enrolAddress memo, memo.sshSig⟩

/-- **The OBSERVED signatures**: the memo's two possession signatures, over the
tariff's mint and the observed enrollment address.  The Receiver's verifier
answers them before `prepare`; a `false` journals the payment (`miniSigInvalid`,
…), only a verifier error refuses.  An unparsed memo observes nothing. -/
def observations (deployment : Deployment) (durable : Durable) (observation : Observation) :
    Except Reject (List SigQuery) :=
  match parsedMemo observation with
  | none => .ok []
  | some memo =>
      match mintOf deployment durable with
      | none => .error .payUnavailable
      | some mint => .ok [miniQuery mint observation.address memo, sshQuery mint observation.address memo]

/-- The two bits `decideEnrol` reads, from the verifier's `answer`s on exactly the
observed queries.  An unparsed memo needs none (`false, false`; the decision
journals it by its memo reason before reading the bits). -/
def verifiedOf (answer : SigQuery → Option Bool) (deployment : Deployment) (durable : Durable)
    (observation : Observation) : Except Reject Verified :=
  match parsedMemo observation with
  | none => .ok ⟨false, false⟩
  | some memo =>
      match mintOf deployment durable with
      | none => .error .payUnavailable
      | some mint =>
          match answer (miniQuery mint observation.address memo),
              answer (sshQuery mint observation.address memo) with
          | some mini, some ssh => .ok ⟨mini, ssh⟩
          | _, _ => .error .unobserved

/-- **Every bit is an answer on an observed query**: when `verifiedOf` decides
the bits of a parsed memo, the mini bit is `answer` on the mini query and the ssh
bit `answer` on the ssh query, and both queries are the observations. -/
theorem verifiedOf_answers {answer : SigQuery → Option Bool} {deployment : Deployment}
    {durable : Durable} {observation : Observation} {verified : Verified} {memo : Memo}
    (parsed : parsedMemo observation = some memo)
    (decided : verifiedOf answer deployment durable observation = .ok verified) :
    ∃ mint, observations deployment durable observation =
        .ok [miniQuery mint observation.address memo, sshQuery mint observation.address memo] ∧
      answer (miniQuery mint observation.address memo) = some verified.mini ∧
      answer (sshQuery mint observation.address memo) = some verified.ssh := by
  unfold verifiedOf at decided
  rw [parsed] at decided
  simp only at decided
  split at decided
  · cases decided
  · rename_i mint minted
    refine ⟨mint, by simp [observations, parsed, minted], ?_⟩
    split at decided
    · rename_i mini ssh miniEq sshEq
      cases decided
      exact ⟨miniEq, sshEq⟩
    · cases decided

/-- **The one claim**: the observer's current key over the envelope's own signed
header (a key lookup and a decode, as the observation family's), for either
enrollment family's refusal type. -/
def envelopeClaims {R : Type} (unavailable : R) (signature : CredentialSignatureAdmission.Reject → R)
    (deployment : Deployment) (durable : Durable) (ingress : DecodedIngress) :
    Except R (List SigQuery) :=
  match loadDeployment deployment durable.snapshot with
  | none => .error unavailable
  | some authority =>
      match CredentialSignatureAdmission.envelopeClaim authority.snapshot ingress.command.observer
          ingress.ingress.envelope with
      | .error reason => .error (signature reason)
      | .ok claim => .ok [claim]

def claims (deployment : Deployment) (durable : Durable) (ingress : DecodedIngress) :
    Except Reject (List SigQuery) :=
  envelopeClaims .authorityUnavailable .signature deployment durable ingress

end Signatures

/-! ## The gate -/

section Gate

variable {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {command : Command} {verified : Verified}

/-- The observer's self-enrollment request bound to the factory's committed head
on the enrollment step (`ComposedPolicyAdmission.Bound`).  The factory's law
verdict is the Receiver's, on the factory write. -/
@[irreducible] def Authorization (planned : Planned deployment profile ambient durable command verified) :
    Type :=
  ComposedPolicyAdmission.Bound (policyConfig planned)
    (request deployment planned.authority.snapshot planned.pay.cell profile.semantics ambient
      command planned.declaration)

def Authorization.of {planned : Planned deployment profile ambient durable command verified}
    (bound : ComposedPolicyAdmission.Bound (policyConfig planned)
      (request deployment planned.authority.snapshot planned.pay.cell profile.semantics ambient
        command planned.declaration)) : Authorization planned := by
  unfold Authorization
  exact bound

def Authorization.bound {planned : Planned deployment profile ambient durable command verified}
    (authorization : Authorization planned) :
    ComposedPolicyAdmission.Bound (policyConfig planned)
      (request deployment planned.authority.snapshot planned.pay.cell profile.semantics ambient
        command planned.declaration) := by
  unfold Authorization at authorization
  exact authorization

end Gate

/-- A prepared enrollment: the Receiver's answers as bits, the plan under them,
the capability-mode receipt built from the Receiver's voucher, and the observer's
request bound to the factory's committed head.  Every law verdict is the
Receiver's. -/
structure Prepared {F : Type} [Field F] [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (ingress : DecodedIngress) where
  private mk ::
  verified : Verified
  planned : Planned deployment profile ambient durable ingress.command verified
  receipt : CredentialSignatureAdmission.CheckedSignature planned.authority.snapshot
  /-- The receipt is the Receiver's: its oracle answered the claim the envelope
  admission checked, before `prepare` ran. -/
  receiptVouched : ∃ oracle, receipt.source = .receiver oracle
  envelopeExact : receipt.envelopeBytes = ingress.ingress.envelope
  authorized : Authorization planned

/-- **What every `Prepared` enrollment means** (layer 1 over layer-2 parts): its
plan is sound (`Planned.sound`), its receipt is the Receiver's for the envelope
the ingress carries, and the observer's request is bound to the factory's
committed head.  The signature verdicts themselves are the oracle's (layer 2). -/
theorem Prepared.sound {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
    {ingress : DecodedIngress} (prepared : Prepared deployment profile ambient durable ingress) :
    (∃ oracle, prepared.receipt.source = .receiver oracle) ∧
      prepared.receipt.envelopeBytes = ingress.ingress.envelope ∧
      prepared.authorized.bound.law.binding
        (request deployment prepared.planned.authority.snapshot prepared.planned.pay.cell
          profile.semantics ambient ingress.command prepared.planned.declaration) = true :=
  ⟨prepared.receiptVouched, prepared.envelopeExact, prepared.authorized.bound.bound⟩

/-- The gate: the bits from the Receiver's answers, the plan, the receipt from the
Receiver's voucher, the observer's capability evidence under it, the request bound
to the factory's committed head.  It judges no law. -/
def prepare {F : Type} [Field F] [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (received : CredentialSignatureAdmission.Received)
    (ambient : Ambient) (durable : Durable) (ingress : DecodedIngress) :
    Except Reject (Prepared deployment profile ambient durable ingress) :=
  match verifiedOf received.vouchers.answer? deployment durable ingress.command.observation with
  | .error reason => .error reason
  | .ok verified =>
  match plan deployment profile ambient durable ingress.command verified with
  | .error reason => .error reason
  | .ok planned =>
    let wanted := request deployment planned.authority.snapshot planned.pay.cell profile.semantics
      ambient ingress.command planned.declaration
    match checked : CredentialSignatureAdmission.CheckedSignature.ofReceiverClaim received
        planned.authority.snapshot
        (marker planned.authority.snapshot.domain profile.semantics ingress.command) wanted
        ingress.ingress.envelope with
    | .error reason => .error (.signature reason)
    | .ok receipt =>
      let config := policyConfig planned
      match (config.capabilityEvidenceChecked wanted ingress.command.capability () receipt ()
          (fun _ => ())).toOption with
      | none => .error .capabilityRejected
      | some evidence =>
        match config.resolve? with
        | none => .error .policyUnavailable
        | some law =>
          match ComposedPolicyAdmission.bind config wanted evidence law
              (.policy wanted.policyId wanted.policyRevision) rfl rfl with
          | none => .error .policyRejected
          | some authorized =>
            have vouched := CredentialSignatureAdmission.CheckedSignature.ofReceiverClaim_vouched checked
            .ok ⟨verified, planned, receipt, ⟨_, vouched.2.1⟩, vouched.2.2.2.2, Authorization.of authorized⟩

/-- **The bits are the Receiver's answers**: a prepared enrollment's `verified`
is `verifiedOf` over the vouchers' answers it was handed. -/
theorem prepare_verified {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {received : CredentialSignatureAdmission.Received}
    {ambient : Ambient} {durable : Durable} {ingress : DecodedIngress}
    {prepared : Prepared deployment profile ambient durable ingress}
    (ran : prepare deployment profile received ambient durable ingress = .ok prepared) :
    verifiedOf received.vouchers.answer? deployment durable ingress.command.observation =
      .ok prepared.verified := by
  unfold prepare at ran
  split at ran
  · cases ran
  · rename_i verified decided
    split at ran
    · cases ran
    · dsimp only at ran
      split at ran
      · cases ran
      · split at ran
        · cases ran
        · split at ran
          · cases ran
          · split at ran
            · cases ran
            · cases ran
              exact decided

/-! ## The family -/

def transactionId (domain semantics : Digest) (ingress : DecodedIngress) : Digest :=
  ⟨marker domain semantics ingress.command⟩

def event (domain : Digest) (ingress : DecodedIngress) : StableEvent where
  codecVersion := 1
  domain := domain
  eventId := (Sp800185Cshake256.hash "DREGG.PAY.SELF-ENROL.EVENT/v1".toUTF8.toList
    ingress.bytes).digest
  canonicalBytes := ingress.bytes

/-- **The pay self-enrollment family** (PAY §11.4). -/
def payEnrolFamily {F : Type} [Field F] [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) : Minidregg.Kernel.Receiving.Family where
  id := .payEnrol
  Env := Ambient
  Ingress := DecodedIngress
  Command := DecodedIngress
  Reject := Reject
  rejectRepr := inferInstance
  Prepared := fun ambient durable ingress => Prepared deployment profile ambient durable ingress
  decode := decodeIngress
  bytes := DecodedIngress.bytes
  command := id
  claims := fun _ durable ingress => claims deployment durable ingress
  observations := fun _ durable ingress => observations deployment durable ingress.command.observation
  prepare := fun received ambient durable ingress =>
    prepare deployment profile received ambient durable ingress
  writes := fun prepared => writes prepared.planned
  writes_bound := fun prepared => writes_bound prepared.planned
  lawStep := fun prepared write _ => lawStepOf prepared.planned write
  observed := fun prepared => prepared.planned.authority.readGuards
  physicalPostLaw := fun prepared => physicalPostLaw prepared.planned
  txId := fun _ ingress => transactionId deployment.domain profile.semantics ingress
  event := fun _ ingress => event deployment.domain ingress
  nullifiers := fun _ ingress =>
    [nullifier deployment.domain ingress.command.observation,
      tickNullifier deployment.domain ingress.command.tip]
  spent := fun prepared => prepared.planned.legs.nullifiers
  subject := fun ingress => some ingress.command.observer
  witnessBytes := fun ingress => ingress.ingress.envelope.length

/-! ## What a committed enrollment means -/

section Committed

variable {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {ingress : DecodedIngress}

/-- The deployed laws. -/
def laws (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F) :
    ReceivingLaw.Laws Durable :=
  ReceivingLaw.Laws.physical profile.compilerProfile deployment

/-- The factory write every branch makes (an enrollment's through the birth plan,
a renewal's and a journal's beside the Book): the factory at its loaded payload. -/
def factoryWrite {command : Command} {verified : Verified}
    (planned : Planned deployment profile ambient durable command verified) : DataWrite :=
  ResourceBirthController.Concrete.packedWrite deployment.factoryId
    ⟨.declaredObject, planned.factory.payload⟩ ⟨.declaredObject, planned.factory.payload⟩

theorem factoryWrite_mem {command : Command} {verified : Verified}
    (planned : Planned deployment profile ambient durable command verified) :
    factoryWrite planned ∈ writes planned := by
  unfold writes
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (Legs.factory_mem planned.factory planned.legs))

theorem lawStepOf_factory {command : Command} {verified : Verified}
    (planned : Planned deployment profile ambient durable command verified) :
    lawStepOf planned (factoryWrite planned) = some (step planned) := by
  unfold lawStepOf
  rw [ReceivingLaw.livePost_live (cell := ⟨.declaredObject, planned.factory.payload⟩) rfl]
  rfl

/-- The factory write is no birth: the loaded directory holds the factory. -/
theorem factoryWrite_not_birth {command : Command} {verified : Verified}
    (planned : Planned deployment profile ambient durable command verified) :
    ReceivingLaw.physicalBirth durable (factoryWrite planned) = false :=
  ReceivingLaw.physicalBirth_false_of_present planned.directory planned.factory.present

/-- **Every committed enrollment's pay, clock and factory writes were judged by
their own committed laws on the family's steps.**
`Minidregg.Kernel.Receiving.Family.receive_committed_lawful`, instantiated: the pay
law and the factory's law on the enrollment step, the clock's law on the clock
step.  The planted faults for this theorem: the Receiver's judgement removed, and
each step projection dropped. -/
theorem committed_lawful {laws : ReceivingLaw.Laws Durable}
    {oracle : CredentialSignatureIO.Oracle Id}
    {Exact : Durable → DataIntent rootBytes → Type} {Other : Type}
    {append : (state : Durable) → (intent : DataIntent rootBytes) →
      Id (Minidregg.Theory.Receiving.Receiver.Commit (Exact state intent) Other)}
    {bytes : List UInt8}
    {admission : ((payEnrolFamily deployment profile).receiver laws oracle).Admitted ambient durable ingress}
    {witness : Exact durable (((payEnrolFamily deployment profile).receiver laws oracle).intent
      admission.accepted)}
    (committed : ((payEnrolFamily deployment profile).receiver laws oracle).receive append ambient
      durable bytes = pure (.committed ingress admission witness)) :
    let planned := admission.accepted.prepared.planned
    ReceivingLaw.Lawful laws .payEnrol durable (writes planned) (payWrite planned)
        (some (step planned)) ∧
      ReceivingLaw.Lawful laws .payEnrol durable (writes planned) (clockWrite planned)
        (some planned.clockStep) ∧
      ReceivingLaw.Lawful laws .payEnrol durable (writes planned) (factoryWrite planned)
        (some (step planned)) := by
  intro planned
  have judged := Minidregg.Kernel.Receiving.Family.receive_committed_lawful
    (payEnrolFamily deployment profile) committed
  have payMem : payWrite planned ∈ writes planned := List.Mem.head _
  have clockMem : clockWrite planned ∈ writes planned := List.Mem.tail _ (List.Mem.head _)
  have factoryMem := factoryWrite_mem planned
  refine ⟨?_, ?_, ?_⟩
  · have lawful := judged (payWrite planned) payMem
    have stepEq : (payEnrolFamily deployment profile).lawStep admission.accepted.prepared
        (payWrite planned) payMem = some (step planned) := by
      dsimp only [payEnrolFamily]
      exact lawStepOf_pay planned
    rwa [stepEq] at lawful
  · have lawful := judged (clockWrite planned) clockMem
    have stepEq : (payEnrolFamily deployment profile).lawStep admission.accepted.prepared
        (clockWrite planned) clockMem = some planned.clockStep := by
      dsimp only [payEnrolFamily]
      exact lawStepOf_clock planned
    rwa [stepEq] at lawful
  · have lawful := judged (factoryWrite planned) factoryMem
    have stepEq : (payEnrolFamily deployment profile).lawStep admission.accepted.prepared
        (factoryWrite planned) factoryMem = some (step planned) := by
      dsimp only [payEnrolFamily]
      exact lawStepOf_factory planned
    rwa [stepEq] at lawful

/-- **One judge, nothing weakened.**  Under the deployed laws, every committed
enrollment satisfies the full compiled admission the family's `prepare` no
longer runs itself: the observer's self-enrollment request, bound to the
factory's committed head (`Prepared.authorized`), with the factory law's
compiled verdict -- which the Receiver judged on the factory write
(`committed_lawful`): the law it resolved is the bound law
(`PhysicalLawResolution.bound_verifies_of_target_judged`). -/
theorem committed_admitted {oracle : CredentialSignatureIO.Oracle Id}
    {Exact : Durable → DataIntent rootBytes → Type} {Other : Type}
    {append : (state : Durable) → (intent : DataIntent rootBytes) →
      Id (Minidregg.Theory.Receiving.Receiver.Commit (Exact state intent) Other)}
    {bytes : List UInt8}
    {admission : ((payEnrolFamily deployment profile).receiver (laws deployment profile) oracle).Admitted
      ambient durable ingress}
    {witness : Exact durable
      (((payEnrolFamily deployment profile).receiver (laws deployment profile) oracle).intent
        admission.accepted)}
    (committed : ((payEnrolFamily deployment profile).receiver (laws deployment profile) oracle).receive
      append ambient durable bytes = pure (.committed ingress admission witness)) :
    let planned := admission.accepted.prepared.planned
    let bound := admission.accepted.prepared.authorized.bound
    ∃ authorized, ComposedPolicyAdmission.admit (policyConfig planned)
      (request deployment planned.authority.snapshot planned.pay.cell profile.semantics ambient
        ingress.command planned.declaration)
      bound.evidence bound.law.witness bound.membership bound.epochExact bound.revisionExact =
        some authorized := by
  intro planned bound
  apply bound.admit_of_verifies
  obtain ⟨-, -, factoryLawful⟩ := committed_lawful committed
  obtain ⟨kind, -, judgedFactory⟩ := factoryLawful
  have notBirth := factoryWrite_not_birth planned
  rcases judgedFactory with ⟨-, judgedStep, law, stepEq, resolvedOf, lowerable, inRange, casts,
      evaluated⟩ | ⟨-, -, -, noStep⟩ | ⟨-, -, (⟨birth, -⟩ | ⟨-, -, noStep⟩)⟩
  · cases stepEq
    have resolved : (laws deployment profile).resolve durable (factoryWrite planned).cellId.value
        (step planned) = some law := by
      unfold ReceivingLaw.lawOf at resolvedOf
      rw [if_neg (by
        show ¬ (ReceivingLaw.physicalBirth durable (factoryWrite planned) = true)
        rw [notBirth]; simp)] at resolvedOf
      exact resolvedOf
    obtain ⟨directory, authority, structural, sources, judged, directoryEq, authorityEq, -, -,
        judgedEq, rfl⟩ :=
      (ReceivingLaw.physical_resolve_some_iff _ _ _ _ _ _).1 resolved
    rw [planned.directoryExact] at directoryEq
    rw [planned.authorityExact] at authorityEq
    cases directoryEq
    cases authorityEq
    have restrictions : ((WorldKindLawDependencies.loadTarget deployment planned.directory.directory
        deployment.factoryId).map (·.additional) |>.getD []) = planned.dependencies.additional := by
      rw [planned.dependenciesExact]
      rfl
    simp only at lowerable inRange casts evaluated
    exact PhysicalLawResolution.bound_verifies_of_target_judged deployment profile.compilerProfile
      planned.authority.snapshot planned.directory.directory _ _ (step planned) deployment.factoryId
      planned.dependencies.additional restrictions judged judgedEq lowerable inRange casts evaluated
      bound
  · cases noStep
  · exact absurd (notBirth.symm.trans birth) (by simp)
  · cases noStep

/-- **The memo's bits are the verifier's answers.**  In every committed
enrollment whose memo parses, under any `Id` oracle: the Receiver observed exactly
the memo's two possession queries (Ed25519 over `miniFrame`, `SSHSIG` under
`dregg-enrol@v1` over `sshsigMessage`), and the decision's `verified.mini` and
`verified.ssh` are the verifier's answers on exactly those queries. -/
theorem committed_verified {laws : ReceivingLaw.Laws Durable}
    {oracle : CredentialSignatureIO.Oracle Id}
    {Exact : Durable → DataIntent rootBytes → Type} {Other : Type}
    {append : (state : Durable) → (intent : DataIntent rootBytes) →
      Id (Minidregg.Theory.Receiving.Receiver.Commit (Exact state intent) Other)}
    {bytes : List UInt8}
    {admission : ((payEnrolFamily deployment profile).receiver laws oracle).Admitted ambient durable ingress}
    {witness : Exact durable (((payEnrolFamily deployment profile).receiver laws oracle).intent
      admission.accepted)}
    (committed : ((payEnrolFamily deployment profile).receiver laws oracle).receive append ambient
      durable bytes = pure (.committed ingress admission witness))
    {memo : Memo} (parsed : parsedMemo ingress.command.observation = some memo) :
    ∃ mint,
      CredentialSignatureAdmission.receiverVerify oracle
          (miniQuery mint ingress.command.observation.address memo) =
        pure (.ok admission.accepted.prepared.verified.mini) ∧
      CredentialSignatureAdmission.receiverVerify oracle
          (sshQuery mint ingress.command.observation.address memo) =
        pure (.ok admission.accepted.prepared.verified.ssh) := by
  have admitted := (((payEnrolFamily deployment profile).receiver laws oracle).receive_committed
    committed).2.2.1
  obtain ⟨queries, observing, keys, answers⟩ :=
    ((payEnrolFamily deployment profile).receiver laws oracle).admitVia_observed admitted
  have ran := admission.prepared.1
  have decided := prepare_verified (received := ⟨oracle, admission.vouchers⟩) ran
  obtain ⟨mint, observed, miniAnswer, sshAnswer⟩ := verifiedOf_answers parsed decided
  refine ⟨mint, ?_, ?_⟩
  · exact answers _ (Vouchers.answer?_some miniAnswer)
  · exact answers _ (Vouchers.answer?_some sshAnswer)

end Committed

/-! ## The signing header -/

/-- The exact header the observer signs: the request the receiver will rebuild,
over the decision it will reach.  The memo's bits are asked of the same verifier
on the same observed queries the Receiver asks (`observations`, `verifiedOf`).
When preparation refuses, the header is built over an empty declaration
(submission then refuses with the named reason). -/
def signingHeader {F : Type} [Field F] [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (native : CredentialSignatureIO.NativeConfig) (command : Command) :
    IO (Except String CredentialSignedEnvelopeController.SignedHeader) := do
  let some authority := loadDeployment deployment durable.snapshot
    | return .error "authority unavailable"
  let some pay := PayCellDomain.load deployment durable.snapshot
    | return .error "pay cell unavailable"
  let fallback : Declaration :=
    ⟨[], [], command.expectedPayRoot, marker deployment.domain profile.semantics command⟩
  let declaration : Declaration ←
    match observations deployment durable command.observation with
    | .error _ => pure fallback
    | .ok queries =>
      match ← Minidregg.Theory.Receiving.Receiver.observeAll
          (CredentialSignatureAdmission.receiverVerify (.live native)) queries with
      | .error _ => pure fallback
      | .ok answered =>
        let answer := fun query => (answered.find? fun given => given.1 == query).map Prod.snd
        match verifiedOf answer deployment durable command.observation with
        | .error _ => pure fallback
        | .ok verified =>
          match plan deployment profile ambient durable command verified with
          | .ok planned => pure planned.declaration
          | .error _ => pure fallback
  return (CredentialSignatureAdmission.signingHeader authority.snapshot
    (marker deployment.domain profile.semantics command)
    ⟨.program, request deployment authority.snapshot pay.cell profile.semantics ambient command
      declaration⟩).mapError
      (fun reason => s!"pay-enrol signer key: {repr reason}")

#assert_axioms Planned.sound
#assert_axioms Prepared.sound
#assert_axioms verifiedOf_answers
#assert_axioms prepare_verified
#assert_axioms Legs.writes_bound
#assert_axioms Legs.factory_mem
#assert_axioms writes_bound
#assert_axioms lawStepOf_pay
#assert_axioms lawStepOf_clock
#assert_axioms lawStepOf_factory
#assert_axioms factoryWrite_mem
#assert_axioms factoryWrite_not_birth
#assert_axioms committed_lawful
#assert_axioms committed_admitted
#assert_axioms committed_verified

end Minidregg.Kernel.PayEnrolReceiver
