/-
# Kernel.PayBookReceiver — the operator installs deposit addresses and sets the tariff

One receiver, two branches in one command: append a batch of deposit
addresses to the pay cell's `book`, and/or replace the `tariff`.  One command
because both are the same authority (the deployment's factory-management
control capability, under the factory's current law — the authorization key
enrollment and factory-observation provisioning use), write the same cell under
the same pre-root, and share one operation marker; a sum of two commands would
be two ingress families with identical plumbing and nothing to separate.

Authorization, exactly as enrollment/provisioning: the sponsor presents the
control (program) capability on the factory, verb `installPolicy`, the request
is admitted in capability mode (`sourceCapabilityOnlyEvidence`) under the
factory's current law with the operation slot `authority/operation/pay-book`,
and the single-use marker is the intent's durable nullifier.

The decision proper is the pure `decideChange`:
* an empty change is refused (`emptyChange`);
* a tariff must be valid and strictly newer (`tariff_version_monotone`; a
  version `≤` the current one is refused `tariffVersionNotIncreasing`);
* addresses are 32 bytes, appended from the command's `bookStart`, which must
  be the current book size: a present index is refused (`bookIndexPresent`),
  a gap is refused (`bookGap`), and each allocation is enabled only at an
  absent index (`book_write_once`).
There is no clock in the pay cell; time is the clock cell's (`Kernel.ClockCell`).
-/
import Kernel.CapabilityRevocationController
import Kernel.PayCellDomain

namespace Minidregg.Kernel.PayBookReceiver

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
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialAuthorityEffects
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.PolicyInstall
open Minidregg.Theory.Store (Store Patch Op Address)
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev Snapshot := CredentialAuthorityDomain.Snapshot

/-! ## The pure decision -/

/-- Allocate `addresses` at consecutive book indices from `start`. -/
def bookPatch : Nat → List Address32 → Patch PayCell.layout
  | _, [] => []
  | index, address :: rest => .allocate .book index address :: bookPatch (index + 1) rest

/-- A decided change: the book rows to append and the tariff replacement
(current, next).  Its patch is a function of the plan alone. -/
structure Plan where
  bookStart : Nat
  book : List Address32
  tariff : Option (Tariff × Tariff)
  deriving DecidableEq, Repr

def Plan.patch (plan : Plan) : Patch PayCell.layout :=
  bookPatch plan.bookStart plan.book ++
    match plan.tariff with
    | none => []
    | some (current, next) => [.write .tariff () current next]

inductive Reject where
  | malformedIngress | directoryUnavailable | authorityUnavailable | factoryUnavailable
  | payUnavailable | staleAuthority | stalePay
  | emptyChange | malformedAddress | bookIndexPresent | bookGap
  | tariffInvalid | tariffVersionNotIncreasing | enrolIndexUnassigned
  | replayedMarker | validation | physicalPreparation
  | policyUnavailable | capabilityRejected | policyRejected | policyInputRange | policyCastAlias
  | signature (reason : CredentialSignatureAdmission.Reject)
  deriving DecidableEq, Repr

/-- A tariff that turns self-enrollment on names an index already assigned
(to the enrollment float, PAY §11.2); `none` is always ready. -/
def enrolReady (store : PayStore) (next : Tariff) : Bool :=
  match next.enrolIndex with
  | none => true
  | some index => (assignmentAt store index).isSome

def decideTariff (store : PayStore) : Option Tariff → Except Reject (Option (Tariff × Tariff))
  | none => .ok none
  | some next =>
      match tariffOf store with
      | none => .error .payUnavailable
      | some current =>
          if next.valid then
            if current.version < next.version then
              if enrolReady store next then .ok (some (current, next))
              else .error .enrolIndexUnassigned
            else .error .tariffVersionNotIncreasing
          else .error .tariffInvalid

def decideBook (store : PayStore) (bookStart : Nat) (book : List Address32) : Except Reject Unit :=
  if book = [] then .ok ()
  else if book.all (fun address => address.length == 32) then
    if (bookAt store bookStart).isSome then .error .bookIndexPresent
    else if bookStart = bookSize store then .ok ()
    else .error .bookGap
  else .error .malformedAddress

def decideChange (store : PayStore) (bookStart : Nat) (book : List Address32)
    (tariff : Option Tariff) : Except Reject Plan :=
  if book = [] ∧ tariff = none then .error .emptyChange
  else
    match decideTariff store tariff, decideBook store bookStart book with
    | .error reason, _ => .error reason
    | .ok _, .error reason => .error reason
    | .ok pair, .ok () => .ok ⟨bookStart, book, pair⟩

/-! ### Theorems of the decision -/

theorem decideTariff_some (store : PayStore) (next : Tariff)
    (pair : Option (Tariff × Tariff)) (accepted : decideTariff store (some next) = .ok pair) :
    ∃ current, tariffOf store = some current ∧ current.version < next.version ∧
      next.valid ∧ enrolReady store next = true ∧ pair = some (current, next) := by
  unfold decideTariff at accepted
  cases present : tariffOf store with
  | none => simp [present] at accepted
  | some current =>
      simp only [present] at accepted
      by_cases valid : next.valid
      · by_cases newer : current.version < next.version
        · by_cases ready : enrolReady store next = true
          · simp only [valid, newer, ready, if_true, Except.ok.injEq] at accepted
            exact ⟨current, rfl, newer, valid, ready, accepted.symm⟩
          · simp [valid, newer, ready] at accepted
        · simp [valid, newer] at accepted
      · simp [valid] at accepted

/-- An accepted change is exactly the command's rows at the command's start,
with the tariff decision `decideTariff` made and the book decision passed. -/
theorem decideChange_ok (store : PayStore) (bookStart : Nat) (book : List Address32)
    (tariff : Option Tariff) (plan : Plan)
    (accepted : decideChange store bookStart book tariff = .ok plan) :
    decideTariff store tariff = .ok plan.tariff ∧ decideBook store bookStart book = .ok () ∧
      plan.bookStart = bookStart ∧ plan.book = book := by
  unfold decideChange at accepted
  by_cases empty : book = [] ∧ tariff = none
  · simp [empty] at accepted
  · rw [if_neg empty] at accepted
    cases tariffDecided : decideTariff store tariff with
    | error reason => simp [tariffDecided] at accepted
    | ok pair =>
        cases bookDecided : decideBook store bookStart book with
        | error reason => simp [tariffDecided, bookDecided] at accepted
        | ok _ =>
            simp only [tariffDecided, bookDecided, Except.ok.injEq] at accepted
            subst accepted
            exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Tariff versions are strictly monotone.**  An accepted tariff change
replaces exactly the current tariff by a valid one with a larger version. -/
theorem tariff_version_monotone (store : PayStore) (bookStart : Nat) (book : List Address32)
    (next : Tariff) (plan : Plan)
    (accepted : decideChange store bookStart book (some next) = .ok plan) :
    ∃ current, tariffOf store = some current ∧ current.version < next.version ∧
      next.valid ∧ plan.tariff = some (current, next) := by
  obtain ⟨current, present, newer, valid, _, pair⟩ :=
    decideTariff_some store next plan.tariff (decideChange_ok store bookStart book _ plan accepted).1
  exact ⟨current, present, newer, valid, pair⟩

/-- Refuting pole: a valid tariff whose version is not larger than the
current one is refused. -/
theorem tariff_version_not_increasing_refused (store : PayStore) (bookStart : Nat)
    (book : List Address32) (current next : Tariff) (present : tariffOf store = some current)
    (valid : next.valid) (stale : next.version ≤ current.version) :
    decideChange store bookStart book (some next) = .error .tariffVersionNotIncreasing := by
  have tariffRefused : decideTariff store (some next) = .error .tariffVersionNotIncreasing := by
    simp [decideTariff, present, valid, Nat.not_lt.mpr stale]
  simp [decideChange, tariffRefused]

/-- An invalid tariff is refused whatever its version. -/
theorem invalid_tariff_refused (store : PayStore) (bookStart : Nat) (book : List Address32)
    (current next : Tariff) (present : tariffOf store = some current) (invalid : ¬ next.valid) :
    decideChange store bookStart book (some next) = .error .tariffInvalid := by
  have tariffRefused : decideTariff store (some next) = .error .tariffInvalid := by
    simp [decideTariff, present, invalid]
  simp [decideChange, tariffRefused]

/-- A book append starting at an index that is already present is refused. -/
theorem book_present_index_refused (store : PayStore) (bookStart : Nat) (book : List Address32)
    (nonempty : book ≠ []) (shaped : book.all (fun address => address.length == 32) = true)
    (present : (bookAt store bookStart).isSome = true) :
    decideChange store bookStart book none = .error .bookIndexPresent := by
  have bookRefused : decideBook store bookStart book = .error .bookIndexPresent := by
    simp [decideBook, nonempty, shaped, present]
  simp [decideChange, nonempty, decideTariff, bookRefused]

/-- **Book rows are written once**: an allocation in the book is enabled only
at an absent index (an instance of `Store.Op.allocate_enabled_fresh`). -/
theorem book_write_once (store : PayStore) (index : Nat) (address : Address32)
    (enabled : (Op.allocate (L := PayCell.layout) .book index address).Enabled store) :
    bookAt store index = none :=
  Minidregg.Theory.Store.Op.allocate_enabled_fresh store .book index address enabled

theorem bookPatch_allocates (start : Nat) (addresses : List Address32) (op : Op PayCell.layout)
    (member : op ∈ bookPatch start addresses) :
    ∃ index address, op = .allocate .book index address := by
  induction addresses generalizing start with
  | nil => cases member
  | cons head rest induction =>
      rcases List.mem_cons.mp member with same | later
      · exact ⟨start, head, same⟩
      · exact induction (start + 1) later

/-- Every operation of a plan writes the book or the tariff. -/
theorem Plan.writes_book_or_tariff (plan : Plan) (op : Op PayCell.layout)
    (member : op ∈ plan.patch) :
    (∃ index address, op = .allocate .book index address) ∨
      ∃ current next, op = .write .tariff () current next := by
  unfold Plan.patch at member
  rcases List.mem_append.mp member with book | tariff
  · exact Or.inl (bookPatch_allocates _ _ op book)
  · split at tariff
    · cases tariff
    · rename_i current next _
      rcases List.mem_singleton.mp tariff with rfl
      exact Or.inr ⟨current, next, rfl⟩

/-! ### Concrete poles (kernel `decide` on real stores) -/

/-- Satisfiable pole: on the genesis cell, setting a valid version-1 tariff and
appending one row at index 0 is accepted. -/
theorem genesis_change_accepted :
    decideChange genesisStore 0 [List.replicate 32 1] (some exampleTariff) =
      .ok ⟨0, [List.replicate 32 1], some (genesisDefault, exampleTariff)⟩ := by
  decide +kernel

/-- Refuting pole: re-setting the same version is refused. -/
theorem same_version_refused :
    decideChange (genesisStore.set tariffAddress (some exampleTariff)) 0 [] (some exampleTariff) =
      .error .tariffVersionNotIncreasing := by
  decide +kernel

/-- Refuting pole: appending at index 0 when row 0 exists is refused. -/
theorem occupied_row_refused :
    decideChange (genesisStore.set (bookAddress 0) (some (List.replicate 32 1))) 0
      [List.replicate 32 2] none = .error .bookIndexPresent := by
  decide +kernel

/-! ## Command and ingress -/

structure Command where
  sponsor : SubjectId
  control : CapabilityId
  nonce : Nat
  expectedFactoryRoot : Digest
  expectedAuthorityRoot : Digest
  expectedPayRoot : Digest
  bookStart : Nat
  book : List Address32
  tariff : Option Tariff
  deriving DecidableEq, Repr

def commandStream : StreamCodec Command :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product capabilityIdStream
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product digestStream
            (StreamCodec.product digestStream
              (StreamCodec.product digestStream
                (StreamCodec.product StreamCodec.nat
                  (StreamCodec.product (StreamCodec.list bytesStream)
                    (StreamCodec.option tariffStream)))))))))
    (fun c => (c.sponsor, c.control, c.nonce, c.expectedFactoryRoot, c.expectedAuthorityRoot,
      c.expectedPayRoot, c.bookStart, c.book, c.tariff))
    (fun (sponsor, control, nonce, factoryRoot, authorityRoot, payRoot, start, book, tariff) =>
      ⟨sponsor, control, nonce, factoryRoot, authorityRoot, payRoot, start, book, tariff⟩)
    (by intro c; cases c; rfl)

def commandFrame : List UInt8 := "DREGG/PAY/BOOK/v1".toUTF8.toList

def commandCodec : LawfulCodec Command := framed commandFrame commandStream

theorem command_roundtrip (command : Command) :
    commandCodec.decode (commandCodec.encode command) = some command :=
  commandCodec.decode_encode command

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
  framed "DREGG/PAY/BOOK/SIGNED/v1".toUTF8.toList ingressStream

structure DecodedIngress where
  private mk ::
  ingress : Ingress
  command : Command
  canonical : commandCodec.encode command = ingress.commandBytes
  envelope : CredentialSignedEnvelopeController.SignedEnvelope
  envelopeExact : CredentialSignatureAdmission.canonicalEnvelopeCodec.decode ingress.sponsorEnvelope =
    some envelope

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

def marker (domain semantics : Digest) (command : Command) : Nat :=
  (Sp800185Cshake256.hash "DREGG.PAY.BOOK.IDENTITY/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
        StreamCodec.nat))).encode
      (domain, semantics, command.sponsor, command.nonce))).digest.value

/-! ## The effect family over the pay cell -/

def planStream : StreamCodec Plan :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product (StreamCodec.list bytesStream)
        (StreamCodec.option (StreamCodec.product tariffStream tariffStream))))
    (fun plan => (plan.bookStart, plan.book, plan.tariff))
    (fun (start, book, tariff) => ⟨start, book, tariff⟩)
    (by intro plan; cases plan; rfl)

structure Declaration where
  plan : Plan
  expectedPreRoot : Digest
  operationNullifier : Nat

def declarationStream : StreamCodec Declaration :=
  StreamCodec.xmap (StreamCodec.product planStream (StreamCodec.product digestStream StreamCodec.nat))
    (fun d => (d.plan, d.expectedPreRoot, d.operationNullifier))
    (fun (plan, root, nullifier) => ⟨plan, root, nullifier⟩)
    (by intro d; cases d; rfl)

def declarationCodec : LawfulCodec Declaration :=
  ResourceBirthCodec.strictCodec declarationStream.toLawful

def declaration (domain semantics : Digest) (command : Command) (plan : Plan) : Declaration :=
  ⟨plan, command.expectedPayRoot, marker domain semantics command⟩

structure Mode {M : Materializer PayCell.layout Digest} (pre : Materialized M) (d : Declaration) : Type where
  rootExact : d.expectedPreRoot = pre.root

def effectDigest (domain semantics : Digest) (command : Command) (d : Declaration) : Digest :=
  (Sp800185Cshake256.hash "DREGG.PAY.BOOK.EFFECT/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product bytesStream bytesStream))).encode
      (domain, semantics, commandCodec.encode command, declarationCodec.encode d))).digest

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
    (Sp800185Cshake256.hash "DREGG.PAY.BOOK.ARGS/v1".toUTF8.toList
      (commandCodec.encode command ++ bytes)).digest

def request (deployment : Deployment) (snapshot : Snapshot) (pay : PayCell.Cell) (semantics : Digest)
    (ambient : Ambient) (command : Command) (plan : Plan) : Request .program :=
  ((context deployment snapshot semantics ambient command).request declarationCodec
    (effectDigest snapshot.domain semantics command) pay.root
    (marker snapshot.domain semantics command)
    (declaration snapshot.domain semantics command plan)).2

def family (deployment : Deployment) (snapshot : Snapshot) (pay : PayCell.Cell) (semantics : Digest)
    (ambient : Ambient) (command : Command) :
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
  Postcondition := fun d _ post => d.plan.patch.ResultAt pay.logical post
  effectDigest := effectDigest snapshot.domain semantics command
  patch := fun d _ => d.plan.patch
  nullifier := fun d _ => some d.operationNullifier
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

def requireSome {A : Type} (reason : Reject) : Option A → Except Reject A
  | none => .error reason
  | some value => .ok value

/-! ## Preparation -/

structure Prepared {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (command : Command) where
  private mk ::
  directory : LoadedDirectory durable
  authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot
  factory : ResourceTargetAdmission.Observed deployment directory.directory .object
    deployment.factoryId command.expectedFactoryRoot
  pay : PayCellDomain.Loaded deployment durable.snapshot
  plan : Plan
  decided : decideChange pay.cell.logical command.bookStart command.book command.tariff = .ok plan
  candidate : Candidate (family deployment authority.snapshot pay.cell profile.semantics ambient command)
    pay.cell (declaration authority.snapshot.domain profile.semantics command plan) ()
  source : CanonicalCellRegistry.LoadedPolicySource authority.snapshot.domain directory.directory
    (authority.snapshot.authState.policyAddress ⟨deployment.factoryId⟩
      (authority.snapshot.authState.policyRevision ⟨deployment.factoryId⟩))

def prepare {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (command : Command) : Except Reject (Prepared deployment profile ambient durable command) := do
  let directory ← requireSome .directoryUnavailable (loadDirectory durable)
  let authority ← requireSome .authorityUnavailable (loadDeployment deployment durable.snapshot)
  let factory ← requireSome .factoryUnavailable
    (ResourceTargetAdmission.observe deployment directory.directory .object
      deployment.factoryId command.expectedFactoryRoot)
  let pay ← requireSome .payUnavailable (PayCellDomain.load deployment durable.snapshot)
  let snapshot := authority.snapshot
  if command.expectedAuthorityRoot = snapshot.cell.root then
    if rootExact : command.expectedPayRoot = pay.cell.root then
      match decided : decideChange pay.cell.logical command.bookStart command.book command.tariff with
      | .error reason => throw reason
      | .ok plan =>
        let d := declaration snapshot.domain profile.semantics command plan
        if snapshot.spent d.operationNullifier = false then
          match validate PayCell.materializer pay.cell pay.cell.root d.plan.patch with
          | .rejected _ => throw .validation
          | .accepted validated =>
              let source ← requireSome .policyUnavailable (CanonicalCellRegistry.loadPolicySource
                snapshot.domain directory.directory
                (snapshot.authState.policyAddress ⟨deployment.factoryId⟩
                  (snapshot.authState.policyRevision ⟨deployment.factoryId⟩)))
              let candidate : Candidate (family deployment snapshot pay.cell profile.semantics ambient command)
                  pay.cell d () :=
                { preStateBound := rfl
                  modeEvidence := ⟨rootExact⟩
                  validated := validated
                  postcondition := validated.resultAt }
              pure ⟨directory, authority, factory, pay, plan, decided, candidate, source⟩
        else throw .replayedMarker
    else throw .stalePay
  else throw .staleAuthority

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {command : Command}

/-- The pay cell after the change: the validated patch applied to the loaded cell. -/
def Prepared.payPost (prepared : Prepared deployment profile ambient durable command) : PayCell.Cell :=
  prepared.candidate.validated.apply

def project (prepared : Prepared deployment profile ambient durable command)
    (logical : PayStore) : Minidregg.Pred.State :=
  ⟨WorldKindLawDependencies.targetSelectorSlots prepared.directory.directory deployment.factoryId ++
    CanonicalRuntimeProfile.requestSlots
      (request deployment prepared.authority.snapshot prepared.pay.cell profile.semantics ambient command
        prepared.plan) ++
    [("authority/operation/pay-book", 1),
     ("pay/book/size", Int.ofNat (bookSize logical)),
     ("pay/tariff/version", Int.ofNat ((tariffOf logical).map Tariff.version |>.getD 0))] ++
    DeclaredResourceController.bytesSlots "command/bytes" 0 (commandCodec.encode command) ++
    DeclaredResourceController.bytesSlots "resource/bytes" 0
      (PackedCell.bytes Registry prepared.factory.before) ++
    ResourceAuthorityProjection.grantSlots "authority/control" .program command.control
      prepared.authority.snapshot.logical⟩

def step (prepared : Prepared deployment profile ambient durable command) : PolicyStepContext :=
  PolicyStepContext.ofCandidate (project prepared) profile.semantics prepared.candidate

def sourceStore (prepared : Prepared deployment profile ambient durable command) :
    CanonicalPolicyRegistry.PayloadStore :=
  ⟨CanonicalCellRegistry.fetchPolicySource prepared.authority.snapshot.domain
    prepared.directory.directory⟩

/-- The actual management target supplies current ambient and kind restrictions. -/
def kindDependencies (prepared : Prepared deployment profile ambient durable command) :
    Option WorldKindLawDependencies.Dependencies :=
  WorldKindLawDependencies.loadTarget deployment prepared.directory.directory deployment.factoryId

def policyConfig [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command) : ComposedPolicyAdmission.Config F :=
  PhysicalLawResolution.config profile.compilerProfile prepared.authority.snapshot
    prepared.directory.directory
    (sourceCapabilityPortal prepared.authority.snapshot
      (marker prepared.authority.snapshot.domain profile.semantics command))
    (step prepared) deployment.factoryId
    ((kindDependencies prepared).map (·.additional) |>.getD [])

def lawReadGuards (prepared : Prepared deployment profile ambient durable command) :
    Option (List (Nat × Digest)) := do
  let structural ← kindDependencies prepared
  let sources ← PhysicalLawResolution.readGuards prepared.authority.snapshot
    prepared.directory.directory profile.semantics deployment.factoryId structural.additional
  pure (sources ++ structural.readGuards)

abbrev Prepared.SemanticAccepted [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command) :=
  AcceptedCellEffect (portal := (policyConfig prepared).portal)
    (authState := prepared.authority.snapshot.authState)
    (family deployment prepared.authority.snapshot prepared.pay.cell profile.semantics ambient command)
    (request deployment prepared.authority.snapshot prepared.pay.cell profile.semantics ambient command
      prepared.plan)
    prepared.pay.cell
    (declaration prepared.authority.snapshot.domain profile.semantics command prepared.plan) ()

def authorize [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command)
    (receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot) :
    Except Reject prepared.SemanticAccepted := do
  let wanted := request deployment prepared.authority.snapshot prepared.pay.cell profile.semantics
    ambient command prepared.plan
  let config := policyConfig prepared
  let _ ← requireSome .policyUnavailable (kindDependencies prepared)
  let evidence ← requireSome .capabilityRejected
    (config.capabilityEvidenceChecked wanted command.control () receipt () (fun _ => ())).toOption
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
    (prepared : Prepared deployment profile ambient durable command)
    (ingress : DecodedIngress) where
  private mk ::
  receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot
  envelopeExact : receipt.envelopeBytes = ingress.ingress.sponsorEnvelope
  semantic : prepared.SemanticAccepted

def admitNative [DecidableEq F] (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared deployment profile ambient durable command)
    (ingress : DecodedIngress) : IO (Except Reject (Accepted prepared ingress)) := do
  match ← CredentialSignatureAdmission.verifyNative native prepared.authority.snapshot
      (marker prepared.authority.snapshot.domain profile.semantics command)
      (request deployment prepared.authority.snapshot prepared.pay.cell profile.semantics ambient
        command prepared.plan)
      ingress.ingress.sponsorEnvelope with
  | .error reason => return .error (.signature reason)
  | .ok receipt =>
      if same : receipt.envelopeBytes = ingress.ingress.sponsorEnvelope then
        match authorize prepared receipt with
        | .error reason => return .error reason
        | .ok semantic => return .ok ⟨receipt, same, semantic⟩
      else return .error .capabilityRejected

/-- The exact header the sponsor signs, derived from the current pay cell and
authority.  It discloses no decision: a plan exists for any decodable command
whose sponsor has a current key. -/
def signingHeader (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) :
    Except String CredentialSignedEnvelopeController.SignedHeader := do
  let some authority := loadDeployment deployment durable.snapshot
    | .error "authority unavailable"
  let some pay := PayCellDomain.load deployment durable.snapshot
    | .error "pay cell unavailable"
  let plan : Plan := ⟨command.bookStart, command.book,
    match command.tariff, tariffOf pay.cell.logical with
    | some next, some current => some (current, next)
    | _, _ => none⟩
  (CredentialSignatureAdmission.signingHeader authority.snapshot
    (marker deployment.domain profile.semantics command)
    ⟨.program, request deployment authority.snapshot pay.cell profile.semantics ambient command plan⟩).mapError
      (fun reason => s!"pay-book signer key: {repr reason}")

/-! ## The receiver -/

def transactionId (domain semantics : Digest) (ingress : DecodedIngress) : Digest :=
  ⟨marker domain semantics ingress.command⟩

def event (domain _semantics : Digest) (ingress : DecodedIngress) : StableEvent where
  codecVersion := 1
  domain := domain
  eventId := (Sp800185Cshake256.hash "DREGG.PAY.BOOK.EVENT/v1".toUTF8.toList ingress.bytes).digest
  canonicalBytes := ingress.bytes

def nullifier (domain semantics : Digest) (ingress : DecodedIngress) : StableNullifier :=
  CredentialAuthorityReplay.nullifier domain (marker domain semantics ingress.command)

def writes (prepared : Prepared deployment profile ambient durable command) : List DataWrite :=
  [prepared.pay.write prepared.payPost]

def resourceGuard (prepared : Prepared deployment profile ambient durable command) : ReadGuard :=
  ⟨⟨deployment.factoryId⟩,
    rootBytes (LifecycleImage.bytes Registry (.live prepared.factory.before))⟩

def policyGuard (prepared : Prepared deployment profile ambient durable command) : ReadGuard :=
  ⟨⟨prepared.source.readGuard.1⟩, prepared.source.readGuard.2⟩

def readGuards (prepared : Prepared deployment profile ambient durable command) : List ReadGuard :=
  resourceGuard prepared :: policyGuard prepared ::
    (prepared.authority.readGuards ++
      ((lawReadGuards prepared).getD []).map (fun (cellIdValue, root) => (⟨⟨cellIdValue⟩, root⟩ : Minidregg.Kernel.DurableDataIntent.ReadGuard))).filter fun guard => guard.cellId ∉ (writes prepared).map DataWrite.cellId

def PhysicalShape (prepared : Prepared deployment profile ambient durable command) : Prop :=
  ((writes prepared).map DataWrite.cellId).Nodup ∧
    (∀ write ∈ writes prepared, write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
    (∀ write ∈ writes prepared, ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
    (resourceGuard prepared).cellId ∉ (writes prepared).map DataWrite.cellId ∧
    (policyGuard prepared).cellId ∉ (writes prepared).map DataWrite.cellId ∧
    (∀ guard ∈ readGuards prepared, guard.expectedRoot = durable.snapshot.model.roots guard.cellId) ∧
    (lawReadGuards prepared).isSome = true

instance physicalShapeDecidable (prepared : Prepared deployment profile ambient durable command) :
    Decidable (PhysicalShape prepared) := by
  unfold PhysicalShape
  infer_instance

theorem writes_roots_bound (prepared : Prepared deployment profile ambient durable command)
    (write : DataWrite) (member : write ∈ writes prepared) :
    rootBytes write.canonicalPostBytes = write.exactPost := by
  simp only [writes, List.mem_singleton] at member
  subst write
  exact prepared.pay.write_root_bound _

theorem readGuards_readonly (prepared : Prepared deployment profile ambient durable command)
    (shape : PhysicalShape prepared) (guard : ReadGuard) (member : guard ∈ readGuards prepared) :
    guard.cellId ∉ (writes prepared).map DataWrite.cellId := by
  rcases List.mem_cons.mp member with rfl | rest
  · exact shape.2.2.2.1
  · rcases List.mem_cons.mp rest with rfl | authority
    · exact shape.2.2.2.2.1
    · simpa using (List.mem_filter.mp authority).2

structure AcceptedChange [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (ingress : DecodedIngress) where
  private mk ::
  prepared : Prepared deployment profile ambient durable ingress.command
  accepted : PayBookReceiver.Accepted prepared ingress
  physical : PhysicalShape prepared

def admitDecodedNative [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (native : CredentialSignatureIO.NativeConfig) (ingress : DecodedIngress) :
    IO (Except Reject (AcceptedChange deployment profile ambient durable ingress)) := do
  match prepare deployment profile ambient durable ingress.command with
  | .error reason => return .error reason
  | .ok prepared =>
    if physical : PhysicalShape prepared then
      match ← admitNative native prepared ingress with
      | .error reason => return .error reason
      | .ok accepted => return .ok ⟨prepared, accepted, physical⟩
    else return .error .physicalPreparation

variable [DecidableEq F] {ingress : DecodedIngress}

def charge (accepted : AcceptedChange deployment profile ambient durable ingress) :
    ResourceCost.Charge
  | .incidences => 1
  | .turnBytes => ingress.bytes.length
  | .memoryTouches => (writes accepted.prepared).length + (readGuards accepted.prepared).length
  | .storageBytes => ((writes accepted.prepared).map fun write => write.canonicalPostBytes.length).sum
  | .witnessBytes => ingress.ingress.sponsorEnvelope.length
  | .proofWork => 2
  | .feeDebit | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

def intent (accepted : AcceptedChange deployment profile ambient durable ingress) :
    DataIntent rootBytes where
  transactionId := transactionId deployment.domain profile.semantics ingress
  subject := some ingress.command.sponsor
  writes := writes accepted.prepared
  readGuards := readGuards accepted.prepared
  nullifiers := [nullifier deployment.domain profile.semantics ingress]
  exactCharge := charge accepted
  event := event deployment.domain profile.semantics ingress
  postRootsBound := writes_roots_bound accepted.prepared
  guardsReadOnly := readGuards_readonly accepted.prepared accepted.physical

/-- The one cell an accepted change writes is the pay cell. -/
theorem intent_writes_pay_cell (accepted : AcceptedChange deployment profile ambient durable ingress) :
    (intent accepted).writes.map DataWrite.cellId = [PayCellDomain.cellIdOf deployment] := rfl

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

#assert_axioms decideTariff_some
#assert_axioms decideChange_ok
#assert_axioms tariff_version_monotone
#assert_axioms tariff_version_not_increasing_refused
#assert_axioms invalid_tariff_refused
#assert_axioms book_present_index_refused
#assert_axioms book_write_once
#assert_axioms genesis_change_accepted
#assert_axioms same_version_refused
#assert_axioms occupied_row_refused
#assert_axioms command_roundtrip

end Minidregg.Kernel.PayBookReceiver
