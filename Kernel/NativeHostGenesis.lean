/-
# Explicit source-owned native host genesis

This is deployment administration, not a public mutation endpoint. The host
supplies its actual arithmetic/runtime profile and public enrollment records.
No test signer, private key, fixture identity, existing image, or caller-built
authority cell is accepted. The complete zero-history image is derived here.

Initial funds are exact mint postings against the named asset's issuer well;
meter allowance remains a separate resource quantity. Admission checks the
same canonical cell laws and the one-cell authority loader used by turns.
Key shape/enrollment is checked, not private-key possession or policy liveness.
A deliberately denying factory policy is valid deployment configuration.
-/
import Compiler.WorldExecutionContract
import Kernel.ResourceBirthPolicyController
import Kernel.PayClaimLaw
import Kernel.ClockLaw
import Theory.AssertAxioms

namespace Minidregg.Kernel.NativeHostGenesis

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialSigningKey
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

attribute [local irreducible] CanonicalRuntimeProfile.Profile.compilerProfile

/-- A supplied public subject and its initial, explicitly budgeted account.
The account may differ from the subject; neither is inferred from key bytes. -/
structure Enrollment where
  key : KeyRecord
  accountId : Nat
  spendCapabilityId : CapabilityId
  controlCapabilityId : CapabilityId
  /-- Separate observe authority for private factory preparation. Birth or
  policy-control authority does not silently grant this read permission. -/
  factoryObserveCapabilityId : CapabilityId
  initialBalance : Nat
  /-- The account's actual law, also checked after explicit delegation. A
  subject-fixed law intentionally refuses another holder until updated. -/
  accountPredicate : Minidregg.Pred.Pred
  deriving DecidableEq, Repr

structure FactoryController where
  subject : SubjectId
  capabilityId : CapabilityId
  deriving DecidableEq, Repr

/-- The enrolled subject that reports finalized payments to the pay cell
(`PayObservationReceiver`), the identifier of its `observePayment`
capability, and the identifier of the factory controller's control
capability on the pay cell (`payControlCapability`), through which the
observer is replaced at runtime (`observer_replaceable`), and the identifier
of the observer's self-enrollment capability on the factory
(`enrolCapability`, `C_enrol` of PAY §11.4), exercised only through
`PayEnrolReceiver` under the clause `authority/operation/pay-self-enrol` of
the confined factory law (`factoryLaw`, `observer_control_confined`). -/
structure PayObserver where
  subject : SubjectId
  capabilityId : CapabilityId
  controlCapabilityId : CapabilityId
  enrolCapabilityId : CapabilityId
/-- A subject that advances the deployment's one clock cell, and the
identifier of its `C_tick`: a root capability on the clock cell
(`ClockCell.physicalId`) carrying the one verb `tickClock`
(`tickCapability`).  The clock cell's genesis law admits these subjects'
`tickClock`, and, beside it, only the pay operations' forward advance
(`clockPredicate`, `Kernel.ClockLaw`), and the factory law refuses them
everything (`factoryLaw`): a ticker can advance the clock and do nothing else
(`clock_subject_confined`).  The operator's wall-clock ticker is one; a chain
observer that asserts chain time is another. -/
structure ClockTicker where
  subject : SubjectId
  capabilityId : CapabilityId
  deriving DecidableEq, Repr

structure Config where
  deployment : CanonicalCellRegistry.Deployment
  federation : FederationId
  tariff : CreationTariff
  expectedSemantics : Digest
  issuerEpoch : Minidregg.Theory.TypedAuthorization.Epoch
  genesisHeight : Height
  factoryPredicate : Minidregg.Pred.Pred
  enrollments : List Enrollment
  factoryController : FactoryController
  meterAllowance : ResourceCost.Charge
  /-- The payment observer.  When present, genesis installs the pay cell's law
  (`payPredicate`) and the observer's capability on the pay cell; when absent,
  no report is admissible (the pay law is not installed). -/
  payObserver : Option PayObserver := none
  /-- Every subject that may tick the clock.  Empty means the clock stays at
  genesis for the life of the deployment: the clock law admits no one. -/
  clockTickers : List ClockTicker
  /-- `L`: how many heights the node may run past its last certified head
  (`Kernel.SystemCell`, `Kernel.TailBound`).  The operator's tariff line;
  written once into the genesis system cell. -/
  tailBound : Nat

/-- Reuse the policy source's typed postfix language. No Boolean host policy
or parallel evaluator enters the genesis codec. -/
def predicateStream : StreamCodec Minidregg.Pred.Pred where
  encode predicate := (StreamCodec.list PolicyRecordCodec.tokenStream).encode
    (PolicyRecordCodec.encodePred predicate)
  decodePrefix bytes := do
    let (tokens, suffix) ← (StreamCodec.list PolicyRecordCodec.tokenStream).decodePrefix bytes
    let predicate ← PolicyRecordCodec.decodePred tokens
    some (predicate, suffix)
  decodePrefix_encode := by
    intro predicate suffix
    simp [(StreamCodec.list PolicyRecordCodec.tokenStream).decodePrefix_encode,
      PolicyRecordCodec.decodePred_encode]

def enrollmentStream : StreamCodec Enrollment :=
  StreamCodec.xmap
    (StreamCodec.product CredentialSigningKeyCodec.keyRecordStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
          (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
            (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
              (StreamCodec.product StreamCodec.nat predicateStream))))))
    (fun enrollment => (enrollment.key, enrollment.accountId,
      enrollment.spendCapabilityId, enrollment.controlCapabilityId,
      enrollment.factoryObserveCapabilityId, enrollment.initialBalance, enrollment.accountPredicate))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1,
      wire.2.2.2.2.1, wire.2.2.2.2.2.1, wire.2.2.2.2.2.2⟩)
    (by intro enrollment; cases enrollment; rfl)

/-- Finite transport over the existing public-key, predicate, and metering
codecs. Exact scalar arity is required, and the outer codec requires canonical
re-encoding; no optional coordinate acquires an implicit default. -/
abbrev ConfigWire :=
  List Nat × List PolicyRecordCodec.Token × List Enrollment × ResourceCost.Charge × List (Nat × Nat)

def configWireStream : StreamCodec ConfigWire :=
  StreamCodec.product (StreamCodec.list StreamCodec.nat)
    (StreamCodec.product (StreamCodec.list PolicyRecordCodec.tokenStream)
      (StreamCodec.product (StreamCodec.list enrollmentStream)
        (StreamCodec.product DurableReceiverCodec.chargeStream
          (StreamCodec.list (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))

def tickerWire (ticker : ClockTicker) : Nat × Nat := (ticker.subject.value, ticker.capabilityId.value)

def tickerOfWire (wire : Nat × Nat) : ClockTicker := ⟨⟨wire.1⟩, ⟨wire.2⟩⟩

@[simp] theorem tickerOfWire_comp_tickerWire : tickerOfWire ∘ tickerWire = _root_.id := by
  funext ticker
  rfl

def Config.toWire (config : Config) : ConfigWire :=
  ([config.deployment.domain.value, config.deployment.factoryId,
    config.deployment.resourceBookId, config.deployment.authorityCellId,
    config.federation.value, config.tariff.base, config.tariff.perBirth,
    config.tariff.perGrant, config.tariff.perInitialPayloadByte,
    config.tariff.collector, config.tariff.asset, config.expectedSemantics.value,
    config.issuerEpoch, config.genesisHeight, config.factoryController.subject.value,
    config.factoryController.capabilityId.value, config.tailBound] ++
    (match config.payObserver with
     | none => []
     | some observer => [observer.subject.value, observer.capabilityId.value,
         observer.controlCapabilityId.value, observer.enrolCapabilityId.value]),
   PolicyRecordCodec.encodePred config.factoryPredicate,
   config.enrollments, config.meterAllowance, config.clockTickers.map tickerWire)

def Config.ofWire (wire : ConfigWire) : Option Config := do
  let (coordinates, payObserver) ← match wire.1 with
    | [domain, factory, book, authority, federation, base, perBirth, perGrant,
        perByte, collector, asset, semantics, issuerEpoch, height, controller,
        controlCapability, tailBound] =>
        some ((domain, factory, book, authority, federation, base, perBirth, perGrant,
          perByte, collector, asset, semantics, issuerEpoch, height, controller,
          controlCapability, tailBound), none)
    | [domain, factory, book, authority, federation, base, perBirth, perGrant,
        perByte, collector, asset, semantics, issuerEpoch, height, controller,
        controlCapability, tailBound, observer, observerCapability, payControl, enrolCapability] =>
        some ((domain, factory, book, authority, federation, base, perBirth, perGrant,
          perByte, collector, asset, semantics, issuerEpoch, height, controller,
          controlCapability, tailBound),
          some (⟨⟨observer⟩, ⟨observerCapability⟩, ⟨payControl⟩, ⟨enrolCapability⟩⟩ : PayObserver))
    | _ => none
  let (domain, factory, book, authority, federation, base, perBirth, perGrant,
      perByte, collector, asset, semantics, issuerEpoch, height, controller,
      controlCapability, tailBound) := coordinates
  let predicate ← PolicyRecordCodec.decodePred wire.2.1
  some
    { deployment := ⟨⟨domain⟩, factory, book, authority⟩
      federation := ⟨federation⟩
      tariff := ⟨base, perBirth, perGrant, perByte, collector, asset⟩
      expectedSemantics := ⟨semantics⟩
      issuerEpoch := issuerEpoch
      genesisHeight := height
      factoryPredicate := predicate
      enrollments := wire.2.2.1
      factoryController := ⟨⟨controller⟩, ⟨controlCapability⟩⟩
      meterAllowance := wire.2.2.2.1
      payObserver := payObserver
      clockTickers := wire.2.2.2.2.map tickerOfWire
      tailBound := tailBound }

@[simp] theorem Config.ofWire_toWire (config : Config) :
    Config.ofWire config.toWire = some config := by
  rcases config with ⟨_, _, _, _, _, _, _, _, _, _, observer, _, _⟩
  cases observer <;> simp [Config.ofWire, Config.toWire]

/-- Version 4 (BRAID-COMPUTE): ONE source for the two version-3 shapes that met at
the merge: CLOCK-SUBJECT's (the clock tickers, from which the clock cell's law and
each ticker's `C_tick` are derived, beside the optional payment observer) and C14's
(the scalar list carries the tail bound `L` after the factory controller).  Every
version-3 source refuses (`v3_config_refused`); version 2 named the authority cell
as the fourth deployment coordinate. -/
def configFrame : List UInt8 := "DREGG/NATIVE-HOST/GENESIS-SOURCE/v4".toUTF8.toList

def configRawCodec : LawfulCodec Config where
  encode config := configFrame ++ configWireStream.encode config.toWire
  decode bytes :=
    if bytes.take configFrame.length = configFrame then do
      let wire ← configWireStream.toLawful.decode (bytes.drop configFrame.length)
      Config.ofWire wire
    else none
  decode_encode := by
    intro config
    have wire := configWireStream.toLawful.decode_encode config.toWire
    change configWireStream.toLawful.decode (configWireStream.encode config.toWire) =
      some config.toWire at wire
    simp [wire]

def configCodec : LawfulCodec Config := ResourceBirthCodec.strictCodec configRawCodec

@[simp] theorem config_roundtrip (config : Config) :
    configCodec.decode (configCodec.encode config) = some config :=
  configCodec.decode_encode config

theorem config_canonical {bytes : List UInt8} {config : Config}
    (accepted : configCodec.decode bytes = some config) :
    configCodec.encode config = bytes :=
  ResourceBirthCodec.strictCodec_canonical configRawCodec accepted

def retiredConfigFrame : List UInt8 := "DREGG/NATIVE-HOST/GENESIS-SOURCE/v3".toUTF8.toList

/-- A version-3 genesis source (either v3 shape: no tail bound, or no tickers) refuses. -/
theorem v3_config_refused (payload : List UInt8) :
    configCodec.decode (retiredConfigFrame ++ payload) = none := by
  have lengthExact : configFrame.length = retiredConfigFrame.length := by decide +kernel
  have different : retiredConfigFrame ≠ configFrame := by decide +kernel
  have raw : configRawCodec.decode (retiredConfigFrame ++ payload) = none := by
    simp [configRawCodec, lengthExact, different]
  simp [configCodec, ResourceBirthCodec.strictCodec, raw]

/-- The authority clock at genesis: no record has been accepted
(`genesis_revision` below). Key activation uses this clock (the durable
height, `CredentialAuthorityDomainReceiver.clockOf`), not a key epoch. -/
def initialAuthorityRevision : Nat := 0

def Config.Valid {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) : Prop :=
  config.expectedSemantics = profile.semantics ∧
  config.deployment.Valid ∧
  config.enrollments ≠ [] ∧
  (config.enrollments.map (·.key.subject)).Nodup ∧
  (config.enrollments.map (·.key.keyId)).Nodup ∧
  (config.enrollments.map (·.key.publicKey)).Nodup ∧
  (config.enrollments.map (·.accountId) ++
    [config.deployment.factoryId, config.deployment.resourceBookId,
     config.deployment.authorityCellId]).Nodup ∧
  config.tariff.asset ∉ config.enrollments.map (·.accountId) ∧
  (config.factoryController.capabilityId ::
    config.enrollments.flatMap (fun enrollment =>
      [enrollment.spendCapabilityId, enrollment.controlCapabilityId,
       enrollment.factoryObserveCapabilityId]) ++
    (config.payObserver.map (·.capabilityId)).toList ++
    (config.payObserver.map (·.controlCapabilityId)).toList ++
    (config.payObserver.map (·.enrolCapabilityId)).toList).Nodup ∧
  config.factoryController.subject.value ∈ config.enrollments.map (·.key.subject) ∧
  (∀ observer ∈ config.payObserver,
    observer.subject.value ∈ config.enrollments.map (·.key.subject)) ∧
  profile.template.lifetime > 0 ∧
  (∀ enrollment ∈ config.enrollments,
    enrollment.key.algorithm = CredentialSignatureAdmission.ed25519Algorithm ∧
    enrollment.key.publicKey.length = 32 ∧
    enrollment.key.activeFrom ≤ initialAuthorityRevision ∧
    initialAuthorityRevision ≤ enrollment.key.activeUntil) ∧
  -- The clock tickers: enrolled, distinct, never the factory controller, and
  -- their `C_tick` identifiers distinct from every other genesis capability.
  (config.clockTickers.map (·.subject.value)).Nodup ∧
  (∀ ticker ∈ config.clockTickers,
    ticker.subject.value ∈ config.enrollments.map (·.key.subject)) ∧
  config.factoryController.subject.value ∉ config.clockTickers.map (·.subject.value) ∧
  (config.clockTickers.map (·.capabilityId) ++
    config.factoryController.capabilityId ::
    config.enrollments.flatMap (fun enrollment =>
      [enrollment.spendCapabilityId, enrollment.controlCapabilityId,
       enrollment.factoryObserveCapabilityId]) ++
    (config.payObserver.map (·.capabilityId)).toList ++
    (config.payObserver.map (·.controlCapabilityId)).toList ++
    (config.payObserver.map (·.enrolCapabilityId)).toList).Nodup

instance configValidDecidable {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) :
    Decidable (config.Valid profile) := by
  unfold Config.Valid
  infer_instance

def Config.accounts (config : Config) : Finset Nat :=
  (config.enrollments.map (·.accountId) ++
    [config.tariff.asset, config.tariff.collector]).toFinset

/-- Each initial allocation executes the existing conserved posting operation. -/
def fund (asset : Nat) : Book → List Enrollment → Book
  | book, [] => book
  | book, enrollment :: rest =>
      fund asset (book.applyPosting
        ⟨asset, enrollment.accountId, asset, enrollment.initialBalance⟩) rest

@[simp] theorem fund_accounts (asset : Nat) (book : Book) (enrollments : List Enrollment) :
    (fund asset book enrollments).accounts = book.accounts := by
  induction enrollments generalizing book with
  | nil => rfl
  | cons enrollment rest ih => exact ih _

theorem fund_conserves (asset : Nat) (book : Book) (enrollments : List Enrollment)
    (issuerPresent : asset ∈ book.accounts)
    (recipientsPresent : ∀ enrollment ∈ enrollments, enrollment.accountId ∈ book.accounts)
    (selectedAsset : Nat) :
    (fund asset book enrollments).totalAsset selectedAsset = book.totalAsset selectedAsset := by
  induction enrollments generalizing book with
  | nil => rfl
  | cons enrollment rest ih =>
      change (fund asset (book.applyPosting
        ⟨asset, enrollment.accountId, asset, enrollment.initialBalance⟩) rest).totalAsset _ = _
      rw [ih (book.applyPosting
        ⟨asset, enrollment.accountId, asset, enrollment.initialBalance⟩)
        issuerPresent (fun selected member =>
        recipientsPresent selected (List.mem_cons_of_mem _ member))]
      exact Book.applyPosting_conserves book _ issuerPresent
        (recipientsPresent enrollment (List.mem_cons_self)) selectedAsset

def Config.initialBook (config : Config) : Book :=
  fund config.tariff.asset ⟨config.accounts, 0, 0⟩ config.enrollments

/-- Every asset, including the explicit issuer well, starts with total zero.
This holds for all configurations, not just one allocation fixture. -/
theorem initialBook_conserved (config : Config) (asset : Nat) :
    config.initialBook.totalAsset asset = 0 := by
  unfold Config.initialBook
  rw [fund_conserves]
  · simp [Book.totalAsset, Book.balance]
  · simp [Config.accounts]
  · intro enrollment member
    simp only [Config.accounts, List.mem_toFinset, List.mem_append]
    exact Or.inl (List.mem_map.mpr ⟨enrollment, member, rfl⟩)

def policy {F : Type} [Field F] (profile : CanonicalRuntimeProfile.Profile F)
    (config : Config) (identifier : Nat) (predicate : Minidregg.Pred.Pred) : PolicyRecord where
  policyId := ⟨identifier⟩
  version := 0
  domain := config.deployment.domain
  semantics := profile.semantics
  previous := none
  predicate := predicate
  localSelector := {}
  parents := []
  descendants := none
  audience := none
  objectDescriptor := none

/-- The factory law with the payment observer confined (PAY §11.4): the
observer is admitted only on a self-enrollment request (the receiver projects
`ClockLaw.paySelfEnrolSlot = 1`), and every clause of the deployment's own factory law is
reached only by a request that is neither the observer's nor a
self-enrollment.  `observer_control_confined`, `self_enrol_only_observer`. -/
def confinedFactoryLaw (observer : SubjectId) (base : Minidregg.Pred.Pred) : Minidregg.Pred.Pred :=
  .any [
    .all [.eq "request/subject" (Int.ofNat observer.value), .eq ClockLaw.paySelfEnrolSlot 1],
    .all [.not (.eq "request/subject" (Int.ofNat observer.value)), .not (.eq ClockLaw.paySelfEnrolSlot 1),
      base]]

/-- The configured ordinary factory law plus the source-authorized claim
branch, placed INSIDE the observer confinement when an observer is present. -/
def observedFactoryLaw (config : Config) : Minidregg.Pred.Pred :=
  match config.payObserver with
  | none => PayClaimLaw.extend config.factoryPredicate
  | some observer => confinedFactoryLaw observer.subject (PayClaimLaw.extend config.factoryPredicate)

/-- The factory law with every clock ticker confined: a ticker's request is
refused whatever the law beneath says (`factory_refuses_ticker`), and every
other request meets exactly that law (`factory_law_others`). -/
def tickerConfinedLaw (tickers : List ClockTicker) (base : Minidregg.Pred.Pred) :
    Minidregg.Pred.Pred :=
  .all (tickers.map (fun ticker =>
      .not (.eq "request/subject" (Int.ofNat ticker.subject.value))) ++ [base])

/-- The factory law genesis installs: the configured one, confined to the
payment observer's self-enrollment when one is present (`observedFactoryLaw`),
and refusing every clock ticker (`tickerConfinedLaw`). -/
def factoryLaw (config : Config) : Minidregg.Pred.Pred :=
  tickerConfinedLaw config.clockTickers (observedFactoryLaw config)

def factoryPolicy {F : Type} [Field F] (profile : CanonicalRuntimeProfile.Profile F)
    (config : Config) : PolicyRecord :=
  policy profile config config.deployment.factoryId (factoryLaw config)

/-- The clock cell's law (`Kernel.ClockLaw.clockPredicate`): the clock never
goes back; it advances by a ticker's `tickClock`, and, when the deployment has
a payment observer, by a payment observation or a self-enrollment, which write
it beside their own cells and are judged by it (`ReceivingLaw.judgeWrite`). -/
def clockPredicate (config : Config) : Minidregg.Pred.Pred :=
  ClockLaw.clockPredicate (config.clockTickers.map (·.subject)) config.payObserver.isSome

def clockTarget (config : Config) : Nat := Kernel.ClockCell.physicalId config.deployment.domain

def clockPolicy {F : Type} [Field F] (profile : CanonicalRuntimeProfile.Profile F)
    (config : Config) : PolicyRecord :=
  policy profile config (clockTarget config) (clockPredicate config)

def accountPolicy {F : Type} [Field F] (profile : CanonicalRuntimeProfile.Profile F)
    (config : Config) (enrollment : Enrollment) : PolicyRecord :=
  policy profile config enrollment.accountId enrollment.accountPredicate

def rootCapability {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config)
    (kind : ResourceKind) (identifier : CapabilityId) (subject : SubjectId)
    (target : Nat) (verbs : Finset (Verb kind)) : Capability kind where
  id := identifier
  root := identifier
  parent := none
  issuer := profile.template.issuer
  holder := .subject subject
  scope := ⟨.explicit {⟨target⟩}, verbs, profile.template.ownerBudget, none, ∅⟩
  notBefore := config.genesisHeight
  notAfter := config.genesisHeight + profile.template.lifetime
  issuerEpoch := config.issuerEpoch
  policyId := ⟨target⟩
  policyEpoch := 0
  ancestors := ∅
  channels := ∅

def accountCapability {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config)
    (enrollment : Enrollment) : Capability .account :=
  rootCapability profile config .account enrollment.spendCapabilityId
    ⟨enrollment.key.subject⟩ enrollment.accountId
    (ResourceBirthPolicyController.Concrete.ownerVerbs .account)

def controlCapability {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) : Capability .program :=
  rootCapability profile config .program config.factoryController.capabilityId
    config.factoryController.subject config.deployment.factoryId {.installPolicy, .revokeCapability}

def accountControlCapability {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config)
    (enrollment : Enrollment) : Capability .program :=
  rootCapability profile config .program enrollment.controlCapabilityId
    ⟨enrollment.key.subject⟩ enrollment.accountId {.installPolicy, .revokeCapability}

def factoryObserveCapability {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config)
    (enrollment : Enrollment) : Capability .object :=
  rootCapability profile config .object enrollment.factoryObserveCapabilityId
    ⟨enrollment.key.subject⟩ config.deployment.factoryId {.observeObject}

/-- The verb tags the pay cell's controller may exercise: `observeProgram`
(1, to read the cell's root, which every management plan pins),
`delegateProgram` (3, to grant a new observer), `installPolicy` (4, to name
it in the law) and `revokeCapability` (5, to retire the old one). -/
def payControlVerbTags : List Int :=
  [Int.ofNat (CredentialAuthorityEntryCodec.verbTag (Verb.observeProgram : Verb .program)),
   Int.ofNat (CredentialAuthorityEntryCodec.verbTag (Verb.delegateProgram : Verb .program)),
   Int.ofNat (CredentialAuthorityEntryCodec.verbTag (Verb.installPolicy : Verb .program)),
   Int.ofNat (CredentialAuthorityEntryCodec.verbTag (Verb.revokeCapability : Verb .program))]

/-- The pay cell's law: the configured observer may only `observePayment`;
the factory controller may only manage (delegate, install the law, revoke).
Neither can do the other's part. -/
def payPredicate (controller : SubjectId) (observer : PayObserver) : Minidregg.Pred.Pred :=
  .any [
    .all [.eq "request/verb" (Int.ofNat (CredentialAuthorityEntryCodec.verbTag
        (Verb.observePayment : Verb .program))),
      .eq "request/subject" (Int.ofNat observer.subject.value)],
    .all [.eq "request/subject" (Int.ofNat controller.value),
      .memberOf "request/verb" payControlVerbTags]]

def payPolicy {F : Type} [Field F] (profile : CanonicalRuntimeProfile.Profile F)
    (config : Config) (observer : PayObserver) : PolicyRecord :=
  policy profile config (Kernel.PayCell.physicalId config.deployment.domain)
    (payPredicate config.factoryController.subject observer)

/-- The observer's capability: target and policy the pay cell, verb
`observePayment` only. -/
def observerCapability {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) (observer : PayObserver) :
    Capability .program :=
  rootCapability profile config .program observer.capabilityId observer.subject
    (Kernel.PayCell.physicalId config.deployment.domain) {.observePayment}

/-- The factory controller's control of the pay cell (approved by ember
2026-09-30 20:45): `installPolicy` and `revokeCapability`, plus
`delegateProgram` and `observePayment`, because the only runtime path that
grants a capability is delegation and a delegated child carries no verb its
parent lacks, and `observeProgram`, because every management plan reads the
target's root under an observation grant.  The pay law (`payPredicate`)
refuses the controller's own reports. -/
def payControlCapability {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) (observer : PayObserver) :
    Capability .program :=
  rootCapability profile config .program observer.controlCapabilityId
    config.factoryController.subject (Kernel.PayCell.physicalId config.deployment.domain)
    {.observeProgram, .installPolicy, .revokeCapability, .delegateProgram, .observePayment}

/-- `C_enrol` (PAY §11.4): the observer's capability on the factory, verb
`installPolicy` only.  The scope alone would be the whole factory control;
the confined factory law (`factoryLaw`) narrows it to self-enrollment. -/
def enrolCapability {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) (observer : PayObserver) :
    Capability .program :=
  rootCapability profile config .program observer.enrolCapabilityId observer.subject
    config.deployment.factoryId {.installPolicy}

/-- A ticker's `C_tick`: target and policy the clock cell, verb `tickClock` only. -/
def tickCapability {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) (ticker : ClockTicker) :
    Capability .program :=
  rootCapability profile config .program ticker.capabilityId ticker.subject
    (clockTarget config) {.tickClock}

def policies {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) : List PolicyRecord :=
  factoryPolicy profile config :: config.enrollments.map (accountPolicy profile config) ++
    (config.payObserver.map (payPolicy profile config)).toList ++
    [clockPolicy profile config]

def policyEntries (record : PolicyRecord) : List (Minidregg.Theory.Store.Entry CredentialAuthorityState.layout) :=
  [⟨⟨.policyEpoch, record.policyId⟩, (0 : TypedAuthorization.Epoch)⟩,
   ⟨⟨.policyRevision, record.policyId⟩, (record.version : PolicyRevision)⟩,
   ⟨⟨.policyAddress, (record.policyId, record.version)⟩, PolicyRecordCodec.digest record⟩]

/-- A genesis signing key: its current epoch, its record, and the registration
of its key version, exactly as enrollment writes them. -/
def keyEntries (key : KeyRecord) : List (Minidregg.Theory.Store.Entry CredentialAuthorityState.layout) :=
  [⟨⟨.subjectKeyEpoch, ⟨key.subject⟩⟩, key.keyEpoch⟩,
   ⟨⟨.subjectKey, (⟨key.subject⟩, key.keyEpoch)⟩, key⟩,
   CredentialAuthorityEffects.registrationEntry (CredentialAuthorityState.signingKeyRevocation key)]

def capabilityEntry {kind : ResourceKind} (capability : Capability kind) :
    Minidregg.Theory.Store.Entry CredentialAuthorityState.layout :=
  ⟨⟨.capability kind, capability.id⟩, (⟨capability, []⟩ : CredentialAuthorityState.StoredCapability kind)⟩

/-- A genesis capability is installed together with the registration of its
own revocation key, exactly as issuance does: "registered" is presence in the
`registered` plane, and genesis holds no capability it could not revoke. -/
def capabilityEntries {kind : ResourceKind} (capability : Capability kind) :
    List (Minidregg.Theory.Store.Entry CredentialAuthorityState.layout) :=
  [capabilityEntry capability,
   CredentialAuthorityEffects.registrationEntry (.capability capability.id)]

/-- Every genesis authority record, as entries of the one authority cell. -/
def entries {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) :
    List (Minidregg.Theory.Store.Entry CredentialAuthorityState.layout) :=
  ⟨⟨.issuerEpoch, profile.template.issuer⟩, config.issuerEpoch⟩ ::
  capabilityEntries (controlCapability profile config) ++
  (policies profile config).flatMap policyEntries ++
  config.enrollments.flatMap (fun enrollment =>
    keyEntries enrollment.key ++
    capabilityEntries (accountCapability profile config enrollment) ++
    capabilityEntries (accountControlCapability profile config enrollment) ++
    capabilityEntries (factoryObserveCapability profile config enrollment)) ++
  config.payObserver.toList.flatMap (fun observer =>
    capabilityEntries (observerCapability profile config observer)) ++
  config.payObserver.toList.flatMap (fun observer =>
    capabilityEntries (payControlCapability profile config observer)) ++
  config.payObserver.toList.flatMap (fun observer =>
    capabilityEntries (enrolCapability profile config observer)) ++
  config.clockTickers.flatMap (fun ticker => capabilityEntries (tickCapability profile config ticker))

/-- The genesis authority store. -/
def authorityStore {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) :
    Store.Store CredentialAuthorityState.layout :=
  StoreCodec.fromEntries (entries profile config)

/-- The authority clock starts at `initialAuthorityRevision`: the genesis
durable snapshot has accepted no record. -/
theorem genesis_revision (seed : DurableReceiver.Seed) :
    CredentialAuthorityDomainReceiver.clockOf (seed.snapshot ResourceBirthCodec.rootBytes) =
      initialAuthorityRevision := rfl

def pins {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) : FactoryPins where
  factory := ⟨config.deployment.factoryId⟩
  domain := config.deployment.domain
  semantics := profile.semantics
  federation := config.federation
  policyId := (factoryPolicy profile config).policyId
  policyAddress := PolicyRecordCodec.digest (factoryPolicy profile config)
  tariff := config.tariff

/-- A declared cell at birth: its declaration (K-FIELD-CLOSURE) and no field.
It holds exactly the fields its writes later create, and it may create only the
fields it declares here (`Kernel.FieldClosure`); `.closed []` holds none. -/
def declaredPacked (identifier : Nat) (account : Bool) (fields : Kernel.FieldClosure.FieldSet) :
    PackedCell CanonicalCellRegistry.registry :=
  let payload := materialize DeclaredEffectCell.materializer
    (Kernel.FieldClosure.declare identifier fields 0)
  if account then ⟨.accountMetadata, payload⟩ else ⟨.declaredObject, payload⟩

def declaredCell (_config : Config) (identifier : Nat) (account : Bool)
    (fields : Kernel.FieldClosure.FieldSet) : PackedCell CanonicalCellRegistry.registry :=
  declaredPacked identifier account fields

/-- The genesis pay cell: the invalid placeholder tariff, an empty deposit
book and no assignment (`PayCell.genesisStore`). -/
def payCell {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) :
    PackedCell CanonicalCellRegistry.registry :=
  -- This constructor is the explicit zero-history seed route, not a carry.
  -- The seed pins this domain/profile activation together with clock day zero.
  let history := (Sp800185Cshake256.hash WorldExecutionContract.freshActivationCustomization
    ((StreamCodec.product digestStream digestStream).encode
      (config.deployment.domain, profile.semantics))).digest
  let activation : Kernel.PayCell.ComputeActivation := ⟨0, none, history⟩
  let store := Kernel.PayCell.genesisStore.set Kernel.PayCell.computeActivationAddress (some activation)
  ⟨.pay, materialize Kernel.PayCell.materializer store⟩
/-- The genesis clock cell: the clock at zero (`ClockCell.genesisStore`). -/
def clockCell : PackedCell CanonicalCellRegistry.registry :=
  ⟨.clock, materialize Kernel.ClockCell.materializer Kernel.ClockCell.genesisStore⟩

/-- The genesis system cell: nothing certified beyond the seed, under the
operator's tail bound (`SystemCell.genesisStore`). -/
def systemCell (config : Config) : PackedCell CanonicalCellRegistry.registry :=
  ⟨.system, materialize Kernel.SystemCell.materializer (Kernel.SystemCell.genesisStore config.tailBound)⟩

def baseCells {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) :
    List (Nat × PackedCell CanonicalCellRegistry.registry) :=
  [(config.deployment.factoryId, declaredCell config config.deployment.factoryId
      false (.closed [])),
   (config.deployment.resourceBookId, ⟨.resourceBook,
      materialize CanonicalResourcePageMaterializer.materializer
        (CanonicalResourcePageMaterializer.stateOfOption (some config.initialBook))⟩)] ++
  config.enrollments.map (fun enrollment =>
    (enrollment.accountId, declaredCell config enrollment.accountId true (.closed []))) ++
  (policies profile config).map (fun record =>
    (PolicySourceCell.physicalId config.deployment.domain (PolicyRecordCodec.digest record),
      CanonicalCellRegistry.policySourceCell record)) ++
  [(Kernel.PayCell.physicalId config.deployment.domain, payCell profile config),
   (Kernel.ClockCell.physicalId config.deployment.domain, clockCell),
   (Kernel.SystemCell.physicalId config.deployment.domain, systemCell config)]

def physicalCells (cells : List (Nat × PackedCell CanonicalCellRegistry.registry)) :
    List (Digest × List UInt8) :=
  cells.map fun (identifier, cell) =>
    (⟨identifier⟩, ResourceBirthCodec.LifecycleImage.bytes _ (.live cell))

def CellListValid (config : Config)
    (cells : List (Nat × PackedCell CanonicalCellRegistry.registry)) : Prop :=
  (cells.map Prod.fst).Nodup ∧
    ∀ row ∈ cells, CanonicalCellRegistry.CellLaw config.deployment row.1 row.2

instance cellListValidDecidable (config : Config)
    (cells : List (Nat × PackedCell CanonicalCellRegistry.registry)) :
    Decidable (CellListValid config cells) := by
  unfold CellListValid
  infer_instance

attribute [local irreducible] ResourceBirthCodec.rootBytes

set_option genSizeOf false in
/-- A checked bootstrap product. The private constructor prevents arbitrary
seeds from being presented as this source's genesis. No accepted turns exist. -/
structure Built {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) where
  private mk ::
  configured : config.Valid profile
  cells : List (Nat × PackedCell CanonicalCellRegistry.registry)
  cellLaws : CellListValid config cells
  seed : DurableReceiver.Seed
  exactSeed : seed = ⟨[], physicalCells cells, config.meterAllowance⟩
  authority : CredentialAuthorityDomainReceiver.Loaded config.deployment
    (seed.snapshot ResourceBirthCodec.rootBytes)

def Built.image {F : Type} [Field F] {profile : CanonicalRuntimeProfile.Profile F}
    {config : Config} (built : Built profile config) : DurableReceiver.Image :=
  ⟨built.seed, []⟩

@[simp] theorem Built.no_history {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {config : Config}
    (built : Built profile config) : built.image.accepted = [] := rfl

theorem Built.profile_exact {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {config : Config}
    (built : Built profile config) : config.expectedSemantics = profile.semantics :=
  built.configured.1

theorem Built.restore {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {config : Config}
    (built : Built profile config) :
    built.image.restore ResourceBirthCodec.rootBytes =
      some (built.seed.snapshot ResourceBirthCodec.rootBytes) := by
  have unique : (built.seed.cells.map Prod.fst).Nodup := by
    rw [built.exactSeed]
    simpa [physicalCells, List.map_map, Function.comp_def] using
      built.cellLaws.1.map (fun _ _ equal => Digest.mk.inj equal)
  simp [Built.image, DurableReceiver.Image.restore, unique, DurableReceiver.replay]

inductive Error where
  | wireEncoding
  | configuration
  | authorityEntries
  | cellLaws
  | physicalAuthority
  deriving DecidableEq, Repr

/-- Source derivation followed by the actual receiving checks. A profile
disagreement, duplicate enrollment or physical collision refuses before a
native write can be requested. -/
def build {F : Type} [Field F] (profile : CanonicalRuntimeProfile.Profile F)
    (config : Config) : Except Error (Built profile config) := do
  if valid : config.Valid profile then
    if !decide ((entries profile config).map Sigma.fst).Nodup then
      throw .authorityEntries
    let authorityCell := materialize CredentialAuthorityCell.materializer (authorityStore profile config)
    let cells := baseCells profile config ++
      [(config.deployment.authorityCellId,
        CredentialAuthorityDomainReceiver.packedCell authorityCell)]
    if cellLaws : CellListValid config cells then
      let seed : DurableReceiver.Seed := ⟨[], physicalCells cells, config.meterAllowance⟩
      let authority ← match CredentialAuthorityDomainReceiver.loadDeployment config.deployment
          (seed.snapshot ResourceBirthCodec.rootBytes) with
        | none => .error .physicalAuthority
        | some authority => .ok authority
      .ok ⟨valid, cells, cellLaws, seed, rfl, authority⟩
    else .error .cellLaws
  else .error .configuration

theorem invalid_configuration_refused {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config)
    (invalid : ¬config.Valid profile) : build profile config = .error .configuration := by
  simp [build, invalid]

theorem incompatible_profile_refused {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config)
    (incompatible : config.expectedSemantics ≠ profile.semantics) :
    build profile config = .error .configuration :=
  invalid_configuration_refused profile config (fun valid => incompatible valid.1)

theorem duplicate_subjects_refused {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config)
    (duplicate : ¬(config.enrollments.map (·.key.subject)).Nodup) :
    build profile config = .error .configuration := by
  apply invalid_configuration_refused profile config
  rintro ⟨_, _, _, unique, _⟩
  exact duplicate unique

theorem duplicate_key_ids_refused {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config)
    (duplicate : ¬(config.enrollments.map (·.key.keyId)).Nodup) :
    build profile config = .error .configuration := by
  apply invalid_configuration_refused profile config
  rintro ⟨_, _, _, _, unique, _⟩
  exact duplicate unique

theorem duplicate_public_keys_refused {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config)
    (duplicate : ¬(config.enrollments.map (·.key.publicKey)).Nodup) :
    build profile config = .error .configuration := by
  apply invalid_configuration_refused profile config
  rintro ⟨_, _, _, _, _, unique, _⟩
  exact duplicate unique

/-- Decoding supplies no authority. The same builder and checks admit every
decoded source, and malformed/noncanonical bytes refuse before derivation. -/
def buildBytes {F : Type} [Field F] (profile : CanonicalRuntimeProfile.Profile F)
    (bytes : List UInt8) : Except Error ((config : Config) × Built profile config) := do
  let config ← match configCodec.decode bytes with
    | none => .error .wireEncoding
    | some config => .ok config
  let built ← build profile config
  pure ⟨config, built⟩

/-! ## The clock subject (CLOCK-SUBJECT)

Genesis names the clock tickers.  Each holds one `C_tick` (`tickCapability`):
the clock cell as target and policy, the verb `tickClock` alone.  Of
`tickClock` requests, the clock cell's law admits exactly a ticker's
(`ClockLaw.tickClause_eval`, `clock_law_refuses_nonticker_tick`); the
factory law refuses every ticker request (`factory_refuses_ticker`) and leaves
every other request to the deployment's own law (`factory_law_others`).  No
genesis capability of the factory controller carries `tickClock`, and the
clock law refuses the controller's tick (`tick_requires_clock_capability`). -/

/-- **A non-ticker's tick is refused** by the genesis clock law, whatever the
deployment: no pay clause reads `tickClock` (`ClockLaw.clock_refuses_nonticker_tick`). -/
theorem clock_law_refuses_nonticker_tick (config : Config) (old new : Minidregg.Pred.State)
    (subject : Nat) (named : new.get "request/subject" = some (Int.ofNat subject))
    (ticking : new.get "request/verb" = some (Int.ofNat ClockLaw.tickVerbTag))
    (other : subject ∉ config.clockTickers.map (·.subject.value)) :
    Minidregg.Pred.eval (clockPredicate config) old new = false :=
  ClockLaw.clock_refuses_nonticker_tick _ _ old new subject named ticking
    (by simpa [List.map_map, Function.comp_def] using other)

/-- **`factory_refuses_ticker`**: under the confined factory law a ticker's
request is refused, whatever the deployment's own law says: no birth, no key
enrollment, no provisioning, no policy install. -/
theorem factory_refuses_ticker (tickers : List ClockTicker) (base : Minidregg.Pred.Pred)
    (ticker : ClockTicker) (member : ticker ∈ tickers) (old new : Minidregg.Pred.State)
    (byTicker : new.get "request/subject" = some (Int.ofNat ticker.subject.value)) :
    Minidregg.Pred.eval (tickerConfinedLaw tickers base) old new = false := by
  have refused : Minidregg.Pred.evalWith Minidregg.Pred.failClosed
      (.not (.eq "request/subject" (Int.ofNat ticker.subject.value))) old new = false := by
    simp [Minidregg.Pred.evalWith, byTicker]
  unfold Minidregg.Pred.eval tickerConfinedLaw
  rw [Minidregg.Pred.evalWith_all, Bool.eq_false_iff]
  intro all_
  have holds := List.all_eq_true.mp all_ _
    (List.mem_append_left _ (List.mem_map.mpr ⟨ticker, member, rfl⟩))
  rw [refused] at holds
  exact Bool.false_ne_true holds

/-- Every request whose subject is not a ticker meets exactly the deployment's
own factory law. -/
theorem factory_law_others (tickers : List ClockTicker) (base : Minidregg.Pred.Pred)
    (old new : Minidregg.Pred.State) (subject : Nat)
    (named : new.get "request/subject" = some (Int.ofNat subject))
    (other : subject ∉ tickers.map (·.subject.value)) :
    Minidregg.Pred.eval (tickerConfinedLaw tickers base) old new =
      Minidregg.Pred.eval base old new := by
  unfold Minidregg.Pred.eval tickerConfinedLaw
  rw [Minidregg.Pred.evalWith_all, List.all_append]
  have guards : (tickers.map fun ticker =>
      (Minidregg.Pred.Pred.not (.eq "request/subject" (Int.ofNat ticker.subject.value)))).all
      (fun q => Minidregg.Pred.evalWith Minidregg.Pred.failClosed q old new) = true := by
    rw [List.all_eq_true]
    intro q member
    obtain ⟨ticker, tickerMember, rfl⟩ := List.mem_map.mp member
    simp only [Minidregg.Pred.evalWith, named, Option.some.injEq, Int.ofNat.injEq,
      Bool.not_eq_true', decide_eq_false_iff_not]
    intro same
    exact other (List.mem_map.mpr ⟨ticker, tickerMember, same.symm⟩)
  rw [guards]
  simp

/-- **`clock_subject_confined`**: a ticker's `C_tick` is held by the ticker,
names the clock cell as its only target and policy and `tickClock` as its only
verb (no delegation, no policy install, no revocation), and is installed at
genesis; and the factory refuses the ticker every request.  `C_tick` covers
the tick verb on the clock cell and nothing else. -/
theorem clock_subject_confined {F : Type} [Field F] (profile : CanonicalRuntimeProfile.Profile F)
    (config : Config) (ticker : ClockTicker) (member : ticker ∈ config.clockTickers) :
    (tickCapability profile config ticker).holder = .subject ticker.subject ∧
      (tickCapability profile config ticker).scope.targets = .explicit {⟨clockTarget config⟩} ∧
      (tickCapability profile config ticker).scope.verbs = {.tickClock} ∧
      (tickCapability profile config ticker).policyId = ⟨clockTarget config⟩ ∧
      capabilityEntry (tickCapability profile config ticker) ∈ entries profile config ∧
      (factoryPolicy profile config).predicate =
        tickerConfinedLaw config.clockTickers (observedFactoryLaw config) ∧
      (∀ old new, new.get "request/subject" = some (Int.ofNat ticker.subject.value) →
        Minidregg.Pred.eval (factoryPolicy profile config).predicate old new = false) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, fun old new byTicker =>
    factory_refuses_ticker _ _ ticker member old new byTicker⟩
  simp only [entries, capabilityEntries, List.mem_append, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false]
  exact Or.inr ⟨ticker, member, Or.inl rfl⟩

/-- **`tick_requires_clock_capability`** (K-CLOCK's `tick_requires_capability`
at the genesis shape): the factory controller's genesis program capabilities
do not carry `tickClock`, and the clock cell's law refuses the factory
controller's tick (a valid genesis never makes it a ticker).  The sponsor cannot
tick: with no evidence the receiver refuses `capabilityRejected`
(`ClockTickReceiver.tick_requires_capability`), and with any evidence the law
refuses. -/
theorem tick_requires_clock_capability {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (config : Config) (valid : config.Valid profile) :
    Verb.tickClock ∉ (controlCapability profile config).scope.verbs ∧
      (∀ enrollment ∈ config.enrollments,
        Verb.tickClock ∉ (accountControlCapability profile config enrollment).scope.verbs) ∧
      (∀ old new, new.get "request/subject" =
          some (Int.ofNat config.factoryController.subject.value) →
        new.get "request/verb" = some (Int.ofNat ClockLaw.tickVerbTag) →
        Minidregg.Pred.eval (clockPolicy profile config).predicate old new = false) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, notTicker, -⟩ := valid
  refine ⟨by simp [controlCapability, rootCapability], fun _ _ => by
    simp [accountControlCapability, rootCapability], fun old new named ticking => ?_⟩
  exact clock_law_refuses_nonticker_tick config old new _ named ticking notTicker

/-- Request states for the poles: clock ticker 70 (the journey's clock subject),
sponsor 7, the journeys' permit-all base law. -/
def requestState (subject verb : Nat) : Minidregg.Pred.State :=
  ⟨[("request/subject", Int.ofNat subject), ("request/verb", Int.ofNat verb)]⟩

def poleTickers : List ClockTicker := [⟨⟨70⟩, ⟨71⟩⟩]

theorem ticker_factory_refused :
    Minidregg.Pred.eval (tickerConfinedLaw poleTickers (.all [])) ⟨[]⟩ (requestState 70 4) = false := by
  decide +kernel

theorem sponsor_factory_admitted :
    Minidregg.Pred.eval (tickerConfinedLaw poleTickers (.all [])) ⟨[]⟩ (requestState 7 4) = true := by
  decide +kernel

#assert_axioms clock_law_refuses_nonticker_tick
#assert_axioms factory_refuses_ticker
#assert_axioms factory_law_others
#assert_axioms clock_subject_confined
#assert_axioms tick_requires_clock_capability
#assert_axioms ticker_factory_refused
#assert_axioms sponsor_factory_admitted

/-- info: 'Minidregg.Kernel.NativeHostGenesis.genesis_revision' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms genesis_revision
/-- info: 'Minidregg.Kernel.NativeHostGenesis.v3_config_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms v3_config_refused

/-! ## The pay cell's control (PAY §11.4, observer replacement) -/

/-- **The pay law, exactly**: on any request naming a subject and a verb, it
admits the observer's `observePayment` (6) and the controller's
`observeProgram`/`delegateProgram`/`installPolicy`/`revokeCapability`
(1/3/4/5), and nothing else. -/
theorem payLaw_eval (controller : SubjectId) (observer : PayObserver)
    (old new : Minidregg.Pred.State) (subject verb : Nat)
    (named : new.get "request/subject" = some (Int.ofNat subject))
    (verbed : new.get "request/verb" = some (Int.ofNat verb)) :
    Minidregg.Pred.eval (payPredicate controller observer) old new = true ↔
      (verb = 6 ∧ subject = observer.subject.value) ∨
        (subject = controller.value ∧ (verb = 1 ∨ verb = 3 ∨ verb = 4 ∨ verb = 5)) := by
  simp only [Minidregg.Pred.eval, payPredicate, Minidregg.Pred.evalWith_any,
    Minidregg.Pred.evalWith_all, List.any_cons, List.all_cons, List.any_nil, List.all_nil,
    Minidregg.Pred.evalWith, named, verbed, payControlVerbTags,
    CredentialAuthorityEntryCodec.verbTag, Bool.and_true, Bool.or_false, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, Option.some.injEq, List.contains_cons,
    List.contains_nil, beq_iff_eq]
  simp only [Int.ofNat.injEq]

/-- **The observer is replaceable at runtime** (ember, 2026-09-30 20:45): every
genesis with an observer also holds the factory controller's control
capability on the pay cell (delegate, install the law, revoke), and the pay
law admits exactly the controller's management and the observer's reports.
The runtime sequence (revoke the old grant; enroll, delegate to and name the
new observer) is the J-PAY-E2 probe's. -/
theorem observer_replaceable {F : Type} [Field F] (profile : CanonicalRuntimeProfile.Profile F)
    (config : Config) (observer : PayObserver) (present : config.payObserver = some observer) :
    capabilityEntry (payControlCapability profile config observer) ∈ entries profile config ∧
      (payControlCapability profile config observer).holder =
        .subject config.factoryController.subject ∧
      (payControlCapability profile config observer).scope.targets =
        .explicit {⟨Kernel.PayCell.physicalId config.deployment.domain⟩} ∧
      Verb.installPolicy ∈ (payControlCapability profile config observer).scope.verbs ∧
      Verb.revokeCapability ∈ (payControlCapability profile config observer).scope.verbs ∧
      Verb.delegateProgram ∈ (payControlCapability profile config observer).scope.verbs ∧
      (∀ old new subject verb,
        new.get "request/subject" = some (Int.ofNat subject) →
        new.get "request/verb" = some (Int.ofNat verb) →
        (Minidregg.Pred.eval (payPredicate config.factoryController.subject observer) old new = true ↔
          (verb = 6 ∧ subject = observer.subject.value) ∨
            (subject = config.factoryController.subject.value ∧
              (verb = 1 ∨ verb = 3 ∨ verb = 4 ∨ verb = 5)))) := by
  refine ⟨?_, rfl, rfl, by simp [payControlCapability, rootCapability],
    by simp [payControlCapability, rootCapability], by simp [payControlCapability, rootCapability],
    fun old new subject verb named verbed => payLaw_eval _ _ old new subject verb named verbed⟩
  simp [entries, present, capabilityEntries]

/-- Refuting pole: the controller's own report is refused by the law when it
is not the observer. -/
theorem controller_cannot_report (controller : SubjectId) (observer : PayObserver)
    (other : controller.value ≠ observer.subject.value) (old new : Minidregg.Pred.State)
    (named : new.get "request/subject" = some (Int.ofNat controller.value))
    (verbed : new.get "request/verb" = some (Int.ofNat 6)) :
    Minidregg.Pred.eval (payPredicate controller observer) old new = false := by
  have := (payLaw_eval controller observer old new controller.value 6 named verbed).not
  simp only [Bool.not_eq_true] at this
  exact this.mpr (by omega)

/-- Refuting pole: the observer cannot install the pay law or revoke. -/
theorem observer_cannot_manage (controller : SubjectId) (observer : PayObserver)
    (other : controller.value ≠ observer.subject.value) (old new : Minidregg.Pred.State)
    (verb : Nat) (management : verb = 1 ∨ verb = 3 ∨ verb = 4 ∨ verb = 5)
    (named : new.get "request/subject" = some (Int.ofNat observer.subject.value))
    (verbed : new.get "request/verb" = some (Int.ofNat verb)) :
    Minidregg.Pred.eval (payPredicate controller observer) old new = false := by
  have := (payLaw_eval controller observer old new observer.subject.value verb named verbed).not
  simp only [Bool.not_eq_true] at this
  exact this.mpr (by omega)

/-! ## The confined factory law (PAY §11.4, P3b-2) -/

/-- **`observer_control_confined`**: under the confined factory law, every
admitted request whose subject is the observer is a self-enrollment
(`ClockLaw.paySelfEnrolSlot = 1`).  The observer can do nothing else on the factory: no
key enrollment, no birth, no provisioning, no policy install. -/
theorem observer_control_confined (observer : SubjectId) (base : Minidregg.Pred.Pred)
    (old new : Minidregg.Pred.State)
    (admitted : Minidregg.Pred.eval (confinedFactoryLaw observer base) old new = true)
    (byObserver : new.get "request/subject" = some (Int.ofNat observer.value)) :
    new.get ClockLaw.paySelfEnrolSlot = some 1 := by
  simp only [Minidregg.Pred.eval, confinedFactoryLaw, Minidregg.Pred.evalWith_any,
    Minidregg.Pred.evalWith_all, List.any_cons, List.all_cons, List.any_nil, List.all_nil,
    Minidregg.Pred.evalWith, byObserver] at admitted
  by_cases slot : new.get ClockLaw.paySelfEnrolSlot = some 1
  · exact slot
  · simp [slot] at admitted

/-- **`self_enrol_only_observer`**: a self-enrollment request is admitted only
when its subject is the observer, whatever the deployment's own law says. -/
theorem self_enrol_only_observer (observer : SubjectId) (base : Minidregg.Pred.Pred)
    (old new : Minidregg.Pred.State)
    (admitted : Minidregg.Pred.eval (confinedFactoryLaw observer base) old new = true)
    (selfEnrol : new.get ClockLaw.paySelfEnrolSlot = some 1) :
    new.get "request/subject" = some (Int.ofNat observer.value) := by
  simp only [Minidregg.Pred.eval, confinedFactoryLaw, Minidregg.Pred.evalWith_any,
    Minidregg.Pred.evalWith_all, List.any_cons, List.all_cons, List.any_nil, List.all_nil,
    Minidregg.Pred.evalWith, selfEnrol] at admitted
  by_cases subject : new.get "request/subject" = some (Int.ofNat observer.value)
  · exact subject
  · simp at admitted
    exact admitted

/-- Every request of anyone but the observer that is not a self-enrollment
meets exactly the deployment's own law. -/
theorem confined_law_others (observer : SubjectId) (base : Minidregg.Pred.Pred)
    (old new : Minidregg.Pred.State) (subject : Nat) (other : subject ≠ observer.value)
    (named : new.get "request/subject" = some (Int.ofNat subject))
    (ordinary : new.get ClockLaw.paySelfEnrolSlot = none) :
    Minidregg.Pred.eval (confinedFactoryLaw observer base) old new =
      Minidregg.Pred.eval base old new := by
  have distinct : ¬ (some (Int.ofNat subject) = some (Int.ofNat observer.value)) := by
    intro same
    exact other (Int.ofNat.inj (Option.some.inj same))
  simp [Minidregg.Pred.eval, confinedFactoryLaw, Minidregg.Pred.evalWith, named, ordinary]
  exact fun _ => other

/-- Request states for the poles (observer 30, controller 7, the journeys'
permit-all base law). -/
def observerState (slots : List (String × Int)) : Minidregg.Pred.State :=
  ⟨("request/subject", 30) :: slots⟩

def controllerState (slots : List (String × Int)) : Minidregg.Pred.State :=
  ⟨("request/subject", 7) :: slots⟩

theorem observer_self_enrol_admitted :
    Minidregg.Pred.eval (confinedFactoryLaw ⟨30⟩ (.all [])) ⟨[]⟩
      (observerState [(ClockLaw.paySelfEnrolSlot, 1)]) = true := by decide +kernel

theorem observer_enroll_key_refused :
    Minidregg.Pred.eval (confinedFactoryLaw ⟨30⟩ (.all [])) ⟨[]⟩
      (observerState [("authority/operation/enroll-key", 1)]) = false := by decide +kernel

theorem observer_install_refused :
    Minidregg.Pred.eval (confinedFactoryLaw ⟨30⟩ (.all [])) ⟨[]⟩
      (observerState [("request/verb", 4)]) = false := by decide +kernel

theorem controller_enroll_key_admitted :
    Minidregg.Pred.eval (confinedFactoryLaw ⟨30⟩ (.all [])) ⟨[]⟩
      (controllerState [("authority/operation/enroll-key", 1)]) = true := by decide +kernel

theorem controller_self_enrol_refused :
    Minidregg.Pred.eval (confinedFactoryLaw ⟨30⟩ (.all [])) ⟨[]⟩
      (controllerState [(ClockLaw.paySelfEnrolSlot, 1)]) = false := by decide +kernel

/-- Genesis installs the confined law whenever an observer is configured, and
holds the observer's `C_enrol`: the factory as target, verb `installPolicy` only. -/
theorem genesis_confines_observer {F : Type} [Field F] (profile : CanonicalRuntimeProfile.Profile F)
    (config : Config) (observer : PayObserver) (present : config.payObserver = some observer) :
    (factoryPolicy profile config).predicate =
        tickerConfinedLaw config.clockTickers
          (confinedFactoryLaw observer.subject (PayClaimLaw.extend config.factoryPredicate)) ∧
      capabilityEntry (enrolCapability profile config observer) ∈ entries profile config ∧
      (enrolCapability profile config observer).holder = .subject observer.subject ∧
      (enrolCapability profile config observer).scope.targets = .explicit {⟨config.deployment.factoryId⟩} ∧
      (enrolCapability profile config observer).scope.verbs = {.installPolicy} := by
  refine ⟨by simp [factoryPolicy, policy, factoryLaw, observedFactoryLaw, present], ?_, rfl, rfl, rfl⟩
  simp [entries, present, capabilityEntries]

/-- The default claim path remains inside both confinement layers. Its
receiver projects no self-enrollment slot and uses the stable owner subject. -/
theorem factory_default_allows_claim (config : Config) (old new : Minidregg.Pred.State)
    (subject : Nat)
    (named : new.get "request/subject" = some (Int.ofNat subject))
    (operation : new.get PayClaimLaw.operationSlot = some 1)
    (authorized : new.get PayClaimLaw.authorizedSlot = some 1)
    (notSelfEnrol : new.get ClockLaw.paySelfEnrolSlot = none)
    (notTicker : subject ∉ config.clockTickers.map (·.subject.value))
    (notObserver : ∀ observer ∈ config.payObserver, subject ≠ observer.subject.value) :
    Minidregg.Pred.eval (factoryLaw config) old new = true := by
  unfold factoryLaw
  rw [factory_law_others config.clockTickers (observedFactoryLaw config)
    old new subject named notTicker]
  cases observed : config.payObserver with
  | none =>
      simpa [observedFactoryLaw, observed] using
        PayClaimLaw.default_allows_claim config.factoryPredicate old new operation authorized
  | some observer =>
      have other : subject ≠ observer.subject.value := notObserver observer (by simp [observed])
      simp only [observedFactoryLaw, observed]
      rw [confined_law_others observer.subject (PayClaimLaw.extend config.factoryPredicate)
        old new subject other named notSelfEnrol]
      exact PayClaimLaw.default_allows_claim config.factoryPredicate old new operation authorized

/-- An observer cannot use a claim receiver step: unlike its v1 observation
path, the claim projection never carries the self-enrollment marker. -/
theorem observer_cannot_claim (observer : SubjectId) (base : Minidregg.Pred.Pred)
    (old new : Minidregg.Pred.State)
    (named : new.get "request/subject" = some (Int.ofNat observer.value))
    (notSelfEnrol : new.get ClockLaw.paySelfEnrolSlot = none) :
    Minidregg.Pred.eval (confinedFactoryLaw observer (PayClaimLaw.extend base)) old new = false := by
  simp [confinedFactoryLaw, Minidregg.Pred.eval, Minidregg.Pred.evalWith, named, notSelfEnrol]

/-- Even a fully authorized claim cannot bypass ticker confinement. -/
theorem ticker_cannot_claim (config : Config) (ticker : ClockTicker)
    (member : ticker ∈ config.clockTickers) (old new : Minidregg.Pred.State)
    (named : new.get "request/subject" = some (Int.ofNat ticker.subject.value)) :
    Minidregg.Pred.eval (factoryLaw config) old new = false :=
  factory_refuses_ticker config.clockTickers (observedFactoryLaw config) ticker member old new named

/-- All former factory behavior is preserved on states without the new source
operation slot, including the observer's existing self-enrollment branch. -/
theorem factory_ordinary_preserved (config : Config) (old new : Minidregg.Pred.State)
    (ordinary : new.get PayClaimLaw.operationSlot = none) :
    Minidregg.Pred.eval (factoryLaw config) old new =
      Minidregg.Pred.eval (tickerConfinedLaw config.clockTickers
        (match config.payObserver with
          | none => config.factoryPredicate
          | some observer => confinedFactoryLaw observer.subject config.factoryPredicate)) old new := by
  cases observed : config.payObserver <;>
    simp [factoryLaw, observedFactoryLaw, observed, tickerConfinedLaw, confinedFactoryLaw,
      PayClaimLaw.extend, PayClaimLaw.clause, Minidregg.Pred.eval, Minidregg.Pred.evalWith,
      List.all_append, ordinary]

#assert_axioms factory_default_allows_claim
#assert_axioms observer_cannot_claim
#assert_axioms ticker_cannot_claim
#assert_axioms factory_ordinary_preserved

#assert_axioms observer_control_confined
#assert_axioms self_enrol_only_observer
#assert_axioms confined_law_others
#assert_axioms observer_self_enrol_admitted
#assert_axioms observer_enroll_key_refused
#assert_axioms observer_install_refused
#assert_axioms controller_enroll_key_admitted
#assert_axioms controller_self_enrol_refused
#assert_axioms genesis_confines_observer
#assert_axioms payLaw_eval
#assert_axioms observer_replaceable
#assert_axioms controller_cannot_report
#assert_axioms observer_cannot_manage

end Minidregg.Kernel.NativeHostGenesis
