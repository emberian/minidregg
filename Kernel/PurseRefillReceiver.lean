/-
# Kernel.PurseRefillReceiver — the signed refill turn (PAY §2.7, lane P6)

One signed command of the owner of Book account `A`
(`Command`: account, purse task, burn, purse gain) is one turn over
two cells, decided by `PurseRefill.decideRefill`:

* the **purse** (an AgentGrain task object): the refill edge, lowered as the
  task's ordinary four-coordinate declared writes (`AgentGrain.actions`),
  guarded at the purse's exact pre-root (the loaded root, carried in the signed
  request) and admitted by
  the purse's **installed law** evaluated with the refill slot
  (`AgentGrain.refillSlot`) this receiver alone projects;
* the **Book**: `.burn A credit amount` (`AcceptedBatch.ofAdmission`).

Authorization: the owner signs a capability-mode request of kind `account`,
target `A`, verb `transfer`, presenting the owner capability, admitted under
`A`'s current law with the operation slot `authority/operation/purse-refill`
(the `PayAssignmentReceiver` pattern); `decideRefill` checks the owner-grant
fact on that same stored capability.  The effect digest commits to the command
bytes and the decided plan, so the signature binds the burn, the gain and the
purse's pre-state.  The pay cell (the tariff's credit asset) and both laws'
sources enter as read guards.
-/
import Kernel.CapabilityRevocationController
import Kernel.ResourceBirthController
import Kernel.PayCellDomain
import Kernel.PurseRefill

namespace Minidregg.Kernel.PurseRefillReceiver

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
open Minidregg.Kernel.PurseRefill
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialAuthorityEffects
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.PolicyInstall
open Minidregg.Theory.Store (Store Patch Op Address)
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev Snapshot := CredentialAuthorityDomain.Snapshot
abbrev PurseCell := Materialized DeclaredEffectCell.materializer
abbrev BookCell (deployment : Deployment) (directory : Directory Nat Registry) :=
  ResourceBirthController.Concrete.ObservedCell deployment directory deployment.resourceBookId
    .resourceBook

/-! ## Command and ingress -/

structure Command where
  subject : SubjectId
  capability : CapabilityId
  account : Nat
  task : Nat
  amount : Nat
  gain : Nat
  nonce : Nat
  expectedAuthorityRoot : Digest
  deriving DecidableEq, Repr

def commandStream : StreamCodec Command :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product capabilityIdStream
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product StreamCodec.nat
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.product StreamCodec.nat
                (StreamCodec.product StreamCodec.nat digestStream)))))))
    (fun c => (c.subject, c.capability, c.account, c.task, c.amount, c.gain, c.nonce,
      c.expectedAuthorityRoot))
    (fun (subject, capability, account, task, amount, gain, nonce, authorityRoot) =>
      ⟨subject, capability, account, task, amount, gain, nonce, authorityRoot⟩)
    (by intro c; cases c; rfl)

def commandFrame : List UInt8 := "DREGG/PAY/REFILL/v1".toUTF8.toList

def commandCodec : LawfulCodec Command := framed commandFrame commandStream

theorem command_roundtrip (command : Command) :
    commandCodec.decode (commandCodec.encode command) = some command :=
  commandCodec.decode_encode command

theorem command_canonical {bytes : List UInt8} {command : Command}
    (accepted : commandCodec.decode bytes = some command) : commandCodec.encode command = bytes :=
  framed_canonical commandFrame commandStream accepted

structure Ingress where
  commandBytes : List UInt8
  envelope : List UInt8
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap (StreamCodec.product bytesStream bytesStream)
    (fun ingress => (ingress.commandBytes, ingress.envelope))
    (fun (command, envelope) => ⟨command, envelope⟩)
    (by intro ingress; cases ingress; rfl)

def ingressFrame : List UInt8 := "DREGG/PAY/REFILL/SIGNED/v1".toUTF8.toList

def ingressCodec : LawfulCodec Ingress := framed ingressFrame ingressStream

theorem ingress_roundtrip (ingress : Ingress) :
    ingressCodec.decode (ingressCodec.encode ingress) = some ingress :=
  ingressCodec.decode_encode ingress

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
    match envelopeExact : CredentialSignatureAdmission.canonicalEnvelopeCodec.decode
        ingress.envelope with
    | none => none
    | some envelope =>
      some ⟨ingress, command, command_canonical commandExact, envelope, envelopeExact⟩

def DecodedIngress.bytes (ingress : DecodedIngress) : List UInt8 :=
  ingressCodec.encode ingress.ingress

def marker (domain semantics : Digest) (command : Command) : Nat :=
  (Sp800185Cshake256.hash "DREGG.PAY.REFILL.IDENTITY/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
        StreamCodec.nat))).encode
      (domain, semantics, command.subject, command.nonce))).digest.value

/-! ## The effect family over the purse -/

def stateStream : StreamCodec AgentGrain.State :=
  StreamCodec.xmap
    (StreamCodec.product IntStream.intStream (StreamCodec.product IntStream.intStream
      (StreamCodec.product IntStream.intStream IntStream.intStream)))
    (fun s => (s.generation, s.status, s.remaining, s.reserved))
    (fun (g, st, r, h) => ⟨g, st, r, h⟩)
    (by intro s; cases s; rfl)

def planStream : StreamCodec Plan :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat stateStream))))
    (fun p => (p.asset, p.account, p.amount, p.gain, p.before))
    (fun (asset, account, amount, gain, before) => ⟨asset, account, amount, gain, before⟩)
    (by intro p; cases p; rfl)

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

/-- The purse's pre-root is the loaded one: the signed request carries it as
`preStateRoot` and the declaration carries the loaded `before` state, so a
purse that moved between the signing plan and the submission no longer
matches the signed header. -/
def declaration (domain semantics : Digest) (command : Command) (purseRoot : Digest)
    (plan : Plan) : Declaration :=
  ⟨plan, purseRoot, marker domain semantics command⟩

/-- The purse leg as the task's ordinary declared writes: all four old
coordinates compared, the refill edge's new ones written. -/
def scalarCommand (command : Command) (d : Declaration) : DeclaredResourceScalar.Command :=
  ⟨.object, command.task, command.subject, command.capability, 1,
    d.expectedPreRoot, d.operationNullifier,
    AgentGrain.actions command.task d.plan.before d.plan.after⟩

/-- The purse leg's patch: the refill writes, then the kernel's ratchet of the
purse's blinding at the turn's height (K-HIDE-ROTATE). -/
def pursePatch (command : Command) (d : Declaration) (pre : Store effectLayout) (height : Nat) :
    Patch effectLayout :=
  DeclaredResourceScalar.cellPatch (scalarCommand command d) ++
    DeclaredEffectCell.blinding.patch pre height

structure Mode {M : Materializer effectLayout Digest} (pre : Materialized M) (d : Declaration) : Type where
  rootExact : d.expectedPreRoot = pre.root

def effectDigest (domain semantics : Digest) (command : Command) (d : Declaration) : Digest :=
  (Sp800185Cshake256.hash "DREGG.PAY.REFILL.EFFECT/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product bytesStream bytesStream))).encode
      (domain, semantics, commandCodec.encode command, declarationCodec.encode d))).digest

structure Ambient where
  federation : FederationId
  height : Height

def context (snapshot : Snapshot) (semantics : Digest) (ambient : Ambient) (command : Command) :
    RequestContext where
  authority :=
    { kind := .account
      domain := snapshot.domain
      semantics := semantics
      federation := ambient.federation
      subject := command.subject
      subjectKeyEpoch := snapshot.authState.subjectKeyEpoch command.subject
      target := ⟨command.account⟩
      verb := .transfer
      nonce := marker snapshot.domain semantics command
      height := ambient.height
      policyId := ⟨command.account⟩
      policyEpoch := snapshot.authState.policyEpoch ⟨command.account⟩
      policyRevision := snapshot.authState.policyRevision ⟨command.account⟩
      cost := (commandCodec.encode command).length }
  argsDigestBytes := fun bytes =>
    (Sp800185Cshake256.hash "DREGG.PAY.REFILL.ARGS/v1".toUTF8.toList
      (commandCodec.encode command ++ bytes)).digest

def request (snapshot : Snapshot) (purse : PurseCell) (semantics : Digest) (ambient : Ambient)
    (command : Command) (plan : Plan) : Request .account :=
  ((context snapshot semantics ambient command).request declarationCodec
    (effectDigest snapshot.domain semantics command) purse.root
    (marker snapshot.domain semantics command)
    (declaration snapshot.domain semantics command purse.root plan)).2

def family (snapshot : Snapshot) (purse : PurseCell) (semantics : Digest) (ambient : Ambient)
    (command : Command) :
    SemanticEffectFamily effectLayout DeclaredEffectCell.materializer Nat where
  Declaration := Declaration
  declarationCodec := declarationCodec
  pre := purse
  request := fun d => (context snapshot semantics ambient command).request
    declarationCodec (effectDigest snapshot.domain semantics command) purse.root
    d.operationNullifier d
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun d _ => Mode purse d
  Postcondition := fun d _ post => (pursePatch command d purse.logical ambient.height).ResultAt purse.logical post
  effectDigest := effectDigest snapshot.domain semantics command
  patch := fun d _ => pursePatch command d purse.logical ambient.height
  nullifier := fun d _ => some d.operationNullifier
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

def requireSome {A : Type} (reason : Reject) : Option A → Except Reject A
  | none => .error reason
  | some value => .ok value

def bookOf {deployment : Deployment} {directory : Directory Nat Registry}
    (book : BookCell deployment directory) : CanonicalResourceKernel.Book :=
  CanonicalResourceKernel.logicalBook book.payload.logical

/-- The purse law's view of the refill: the slot only this receiver projects,
then the task's exact declared projection from its loaded store to the
candidate post, then who pays and how much. -/
def purseState (command : Command) (pre post : Store effectLayout) : Minidregg.Pred.State :=
  ⟨(AgentGrain.refillSlot, 1) ::
    DeclaredResourceProjection.project command.task pre post ++
    [("request/subject", Int.ofNat command.subject.value),
     ("pay/refill/account", Int.ofNat command.account),
     ("pay/refill/amount", Int.ofNat command.amount)]⟩

/-- The purse the directory holds at `task`, selected as a declared object. -/
structure LoadedPurse (deployment : Deployment) (directory : Directory Nat Registry) (task : Nat) where
  packed : PackedCell Registry
  present : directory.slots task = .present packed
  purse : PurseCell
  selected : CanonicalCellRegistry.selectDeclared deployment task .object packed = some purse

def loadPurse (deployment : Deployment) (directory : Directory Nat Registry) (task : Nat) :
    Option (LoadedPurse deployment directory task) :=
  match present : directory.slots task with
  | .absent => none
  | .present packed =>
      match selected : CanonicalCellRegistry.selectDeclared deployment task .object packed with
      | none => none
      | some purse => some ⟨packed, present, purse, selected⟩

/-! ## Preparation -/

structure Prepared {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (command : Command) where
  private mk ::
  directory : LoadedDirectory durable
  authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot
  pay : PayCellDomain.Loaded deployment durable.snapshot
  book : BookCell deployment directory.directory
  purseBefore : PackedCell Registry
  pursePresent : directory.directory.slots command.task = .present purseBefore
  purse : PurseCell
  purseSelected : CanonicalCellRegistry.selectDeclared deployment command.task .object purseBefore =
    some purse
  plan : Plan
  decided : decideRefill (tariffOf pay.cell.logical)
    (readCapability authority.snapshot.cell .account command.capability) command.subject
    (bookOf book) (AgentGrain.readState command.task purse.logical)
    command.account command.amount command.gain = .ok plan
  resources : CanonicalResourceKernel.AcceptedBatch book.payload plan.batch
  candidate : Candidate (family authority.snapshot purse profile.semantics ambient command)
    purse (declaration authority.snapshot.domain profile.semantics command purse.root plan) ()
  purseLaw : CanonicalCellRegistry.LoadedPolicySource authority.snapshot.domain directory.directory
    (authority.snapshot.authState.policyAddress ⟨command.task⟩
      (authority.snapshot.authState.policyRevision ⟨command.task⟩))
  purseAccepted : Minidregg.Pred.eval purseLaw.record.predicate ⟨[]⟩
    (purseState command purse.logical candidate.validated.apply.logical) = true
  source : CanonicalCellRegistry.LoadedPolicySource authority.snapshot.domain directory.directory
    (authority.snapshot.authState.policyAddress ⟨command.account⟩
      (authority.snapshot.authState.policyRevision ⟨command.account⟩))

/-- The decision, in order: the loaded cells, the pinned authority root, the pure
`decideRefill` (tariff, owner grant, not the issuer, positive, readable purse,
Book admission, balanced joint delta), the marker, the purse's declared-cell
checks and patch validation, the purse's installed law with the refill slot,
and the account law's source.  Refusals before the signature check are named
(the enrollment pattern of this branch). -/
def prepare {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (command : Command) : Except Reject (Prepared deployment profile ambient durable command) := do
  let directory ← requireSome .directoryUnavailable (loadDirectory durable)
  let authority ← requireSome .authorityUnavailable (loadDeployment deployment durable.snapshot)
  let pay ← requireSome .payUnavailable (PayCellDomain.load deployment durable.snapshot)
  let book ← requireSome .bookUnavailable
    (ResourceBirthController.Concrete.observeCell deployment directory.directory
      deployment.resourceBookId .resourceBook)
  let loaded ← requireSome .purseUnavailable (loadPurse deployment directory.directory command.task)
  let purseBefore := loaded.packed
  let present := loaded.present
  let purse := loaded.purse
  let selected := loaded.selected
  let snapshot := authority.snapshot
  if command.expectedAuthorityRoot = snapshot.cell.root then
      match decided : decideRefill (tariffOf pay.cell.logical)
          (readCapability snapshot.cell .account command.capability) command.subject
          (bookOf book) (AgentGrain.readState command.task purse.logical)
          command.account command.amount command.gain with
      | .error reason => throw reason
      | .ok plan =>
        let d := declaration snapshot.domain profile.semantics command purse.root plan
        if snapshot.spent d.operationNullifier = false then
          match DeclaredResourceScalar.prepareCell snapshot profile.semantics
              ⟨ambient.federation, ambient.height⟩ purse (scalarCommand command d) with
          | .error reason => throw (.purseCell reason)
          | .ok _ =>
            match validate DeclaredEffectCell.materializer purse purse.root
                (pursePatch command d purse.logical ambient.height) with
            | .rejected _ => throw .validation
            | .accepted validated =>
              let candidate : Candidate (family snapshot purse profile.semantics ambient command)
                  purse d () :=
                { preStateBound := rfl
                  modeEvidence := ⟨rfl⟩
                  validated := validated
                  postcondition := validated.resultAt }
              let purseLaw ← requireSome .purseLawUnavailable
                (CanonicalCellRegistry.loadPolicySource snapshot.domain directory.directory
                  (snapshot.authState.policyAddress ⟨command.task⟩
                    (snapshot.authState.policyRevision ⟨command.task⟩)))
              if purseAccepted : Minidregg.Pred.eval purseLaw.record.predicate ⟨[]⟩
                  (purseState command purse.logical candidate.validated.apply.logical) = true then
                let source ← requireSome .policyUnavailable
                  (CanonicalCellRegistry.loadPolicySource snapshot.domain directory.directory
                    (snapshot.authState.policyAddress ⟨command.account⟩
                      (snapshot.authState.policyRevision ⟨command.account⟩)))
                pure ⟨directory, authority, pay, book, purseBefore, present, purse, selected, plan,
                  decided,
                  CanonicalResourceKernel.AcceptedBatch.ofAdmission
                    (decideRefill_ok decided).2.2.2.2.2.2.2.2.1,
                  candidate, purseLaw, purseAccepted, source⟩
              else throw .purseRefused
        else throw .replayedMarker
  else throw .staleAuthority

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {command : Command}

def Prepared.pursePost (prepared : Prepared deployment profile ambient durable command) : PurseCell :=
  prepared.candidate.validated.apply

def Prepared.bookPost (prepared : Prepared deployment profile ambient durable command) :
    Materialized (CanonicalCellRegistry.materializer .resourceBook) :=
  prepared.resources.post

/-- The prepared Book is exactly the burn applied to the loaded Book. -/
theorem Prepared.bookPost_exact (prepared : Prepared deployment profile ambient durable command) :
    CanonicalResourceKernel.logicalBook prepared.bookPost.logical =
      prepared.plan.batch.apply (bookOf prepared.book) :=
  prepared.resources.post_logicalBook

/-- A prepared refill holds the owner grant on the capability it presents. -/
theorem Prepared.owner (prepared : Prepared deployment profile ambient durable command) :
    PayAssignmentReceiver.OwnerGrant
      (readCapability prepared.authority.snapshot.cell .account command.capability)
      command.subject command.account :=
  refill_requires_owner prepared.decided

/-- A prepared refill's two legs balance at the credit coordinate. -/
theorem Prepared.balanced (prepared : Prepared deployment profile ambient durable command) :
    aggregateDelta (bookOf prepared.book) prepared.plan = 0 :=
  refill_balanced prepared.decided

/-- A prepared refill burned what the purse gains, and the Book conserves. -/
theorem Prepared.conserves (prepared : Prepared deployment profile ambient durable command) :
    (CanonicalResourceKernel.logicalBook prepared.bookPost.logical).totalAsset prepared.plan.asset =
        (bookOf prepared.book).totalAsset prepared.plan.asset ∧
      budget prepared.plan.after = budget prepared.plan.before + Int.ofNat command.amount := by
  rw [prepared.bookPost_exact]
  exact ⟨(refill_conserves prepared.decided).1, (refill_conserves prepared.decided).2.2.2.2.1⟩

/-- The purse leg starts from the purse the Store holds. -/
theorem Prepared.purse_before (prepared : Prepared deployment profile ambient durable command) :
    AgentGrain.readState command.task prepared.purse.logical = some prepared.plan.before :=
  (decideRefill_ok prepared.decided).2.2.2.2.1

def project (prepared : Prepared deployment profile ambient durable command)
    (logical : Store effectLayout) : Minidregg.Pred.State :=
  ⟨CanonicalRuntimeProfile.requestSlots
      (request prepared.authority.snapshot prepared.purse profile.semantics ambient command
        prepared.plan) ++
    [("authority/operation/purse-refill", 1),
     ("pay/refill/task", Int.ofNat command.task),
     ("pay/refill/amount", Int.ofNat command.amount)] ++
    DeclaredResourceProjection.project command.task prepared.purse.logical logical ++
    DeclaredResourceController.bytesSlots "command/bytes" 0 (commandCodec.encode command) ++
    ResourceAuthorityProjection.grantSlots "authority/owner" .account command.capability
      prepared.authority.snapshot.logical⟩

def step (prepared : Prepared deployment profile ambient durable command) : PolicyStepContext :=
  PolicyStepContext.ofCandidate (project prepared) profile.semantics prepared.candidate

def sourceStore (prepared : Prepared deployment profile ambient durable command) :
    CanonicalPolicyRegistry.PayloadStore :=
  ⟨CanonicalCellRegistry.fetchPolicySource prepared.authority.snapshot.domain
    prepared.directory.directory⟩

def policyConfig [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command) : CanonicalPolicyConfig F :=
  CredentialAuthorityPolicyRegistry.config profile.compilerProfile prepared.authority.snapshot
    (sourceStore prepared)
    (sourceCapabilityPortal prepared.authority.snapshot
      (marker prepared.authority.snapshot.domain profile.semantics command))
    (step prepared)

abbrev Prepared.SemanticAccepted [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command) :=
  AcceptedCellEffect (portal := (policyConfig prepared).portal)
    (authState := prepared.authority.snapshot.authState)
    (family prepared.authority.snapshot prepared.purse profile.semantics ambient command)
    (request prepared.authority.snapshot prepared.purse profile.semantics ambient command
      prepared.plan)
    prepared.purse
    (declaration prepared.authority.snapshot.domain profile.semantics command prepared.purse.root
      prepared.plan) ()

def authorize [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command)
    (receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot) :
    Except Reject prepared.SemanticAccepted := do
  let wanted := request prepared.authority.snapshot prepared.purse profile.semantics ambient
    command prepared.plan
  let config := policyConfig prepared
  let evidence ← requireSome .capabilityRejected
    (sourceCapabilityOnlyEvidence profile.compilerProfile prepared.authority.snapshot
      (sourceStore prepared)
      (marker prepared.authority.snapshot.domain profile.semantics command) (step prepared)
      wanted command.capability receipt)
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
    (prepared : Prepared deployment profile ambient durable command)
    (ingress : DecodedIngress) where
  private mk ::
  receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot
  envelopeExact : receipt.envelopeBytes = ingress.ingress.envelope
  semantic : prepared.SemanticAccepted

def admitNative [DecidableEq F] (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared deployment profile ambient durable command)
    (ingress : DecodedIngress) : IO (Except Reject (Accepted prepared ingress)) := do
  match ← CredentialSignatureAdmission.verifyNative native prepared.authority.snapshot
      (marker prepared.authority.snapshot.domain profile.semantics command)
      (request prepared.authority.snapshot prepared.purse profile.semantics ambient command
        prepared.plan)
      ingress.ingress.envelope with
  | .error reason => return .error (.signature reason)
  | .ok receipt =>
      if same : receipt.envelopeBytes = ingress.ingress.envelope then
        match authorize prepared receipt with
        | .error reason => return .error reason
        | .ok semantic => return .ok ⟨receipt, same, semantic⟩
      else return .error .capabilityRejected

/-- The exact header the owner signs.  It discloses no decision: when the
command does not decide, it is built over a plan that echoes the command at the
loaded purse (and submission then refuses with the named reason). -/
def signingHeader (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) :
    Except String CredentialSignedEnvelopeController.SignedHeader := do
  let some authority := loadDeployment deployment durable.snapshot
    | .error "authority unavailable"
  let some pay := PayCellDomain.load deployment durable.snapshot
    | .error "pay cell unavailable"
  let some directory := loadDirectory durable
    | .error "directory unavailable"
  let some book := ResourceBirthController.Concrete.observeCell deployment directory.directory
      deployment.resourceBookId .resourceBook
    | .error "book unavailable"
  let .present purseBefore := directory.directory.slots command.task
    | .error "purse unavailable"
  let some purse := CanonicalCellRegistry.selectDeclared deployment command.task .object purseBefore
    | .error "purse unavailable"
  let before := (AgentGrain.readState command.task purse.logical).getD ⟨0, 0, 0, 0⟩
  let plan : Plan :=
    match decideRefill (tariffOf pay.cell.logical)
        (readCapability authority.snapshot.cell .account command.capability) command.subject
        (bookOf book) (AgentGrain.readState command.task purse.logical)
        command.account command.amount command.gain with
    | .ok plan => plan
    | .error _ => ⟨((tariffOf pay.cell.logical).map Tariff.asset).getD 0, command.account,
        command.amount, command.gain, before⟩
  (CredentialSignatureAdmission.signingHeader authority.snapshot
    (marker deployment.domain profile.semantics command)
    ⟨.account, request authority.snapshot purse profile.semantics ambient command plan⟩).mapError
      (fun reason => s!"pay-refill signer key: {repr reason}")

/-! ## The receiver -/

def transactionId (domain semantics : Digest) (ingress : DecodedIngress) : Digest :=
  ⟨marker domain semantics ingress.command⟩

def event (domain _semantics : Digest) (ingress : DecodedIngress) : StableEvent where
  codecVersion := 1
  domain := domain
  eventId := (Sp800185Cshake256.hash "DREGG.PAY.REFILL.EVENT/v1".toUTF8.toList
    ingress.bytes).digest
  canonicalBytes := ingress.bytes

def nullifier (domain semantics : Digest) (ingress : DecodedIngress) : StableNullifier :=
  CredentialAuthorityReplay.nullifier domain (marker domain semantics ingress.command)

def purseWrite (prepared : Prepared deployment profile ambient durable command) : DataWrite :=
  ResourceBirthController.Concrete.packedWrite command.task prepared.purseBefore
    (DeclaredResourceScalar.packDeclared .object prepared.pursePost)

def bookWrite (prepared : Prepared deployment profile ambient durable command) : DataWrite :=
  ResourceBirthController.Concrete.packedWrite deployment.resourceBookId
    ⟨.resourceBook, prepared.book.payload⟩ ⟨.resourceBook, prepared.bookPost⟩

def writes (prepared : Prepared deployment profile ambient durable command) : List DataWrite :=
  [purseWrite prepared, bookWrite prepared]

def policyGuard (prepared : Prepared deployment profile ambient durable command) : ReadGuard :=
  ⟨⟨prepared.source.readGuard.1⟩, prepared.source.readGuard.2⟩

def purseLawGuard (prepared : Prepared deployment profile ambient durable command) : ReadGuard :=
  ⟨⟨prepared.purseLaw.readGuard.1⟩, prepared.purseLaw.readGuard.2⟩

/-- The tariff (the credit asset) is read at the pay cell's exact root. -/
def payGuard (prepared : Prepared deployment profile ambient durable command) : ReadGuard :=
  ⟨PayCellDomain.cellIdOf deployment, PayCellDomain.cellRoot prepared.pay.cell⟩

def sourceGuards (prepared : Prepared deployment profile ambient durable command) : List ReadGuard :=
  [policyGuard prepared, purseLawGuard prepared, payGuard prepared].dedup

def readGuards (prepared : Prepared deployment profile ambient durable command) : List ReadGuard :=
  sourceGuards prepared ++
    prepared.authority.readGuards.filter fun guard =>
      guard.cellId ∉ (writes prepared).map DataWrite.cellId ∧
        guard.cellId ∉ (sourceGuards prepared).map ReadGuard.cellId

def PhysicalShape (prepared : Prepared deployment profile ambient durable command) : Prop :=
  ((writes prepared).map DataWrite.cellId).Nodup ∧
    (∀ write ∈ writes prepared, write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
    (∀ write ∈ writes prepared, ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
    (∀ write ∈ writes prepared, rootBytes write.canonicalPostBytes = write.exactPost) ∧
    (∀ guard ∈ sourceGuards prepared, guard.cellId ∉ (writes prepared).map DataWrite.cellId) ∧
    (∀ guard ∈ readGuards prepared, guard.expectedRoot = durable.snapshot.model.roots guard.cellId)

instance physicalShapeDecidable (prepared : Prepared deployment profile ambient durable command) :
    Decidable (PhysicalShape prepared) := by
  unfold PhysicalShape
  infer_instance

theorem readGuards_readonly (prepared : Prepared deployment profile ambient durable command)
    (shape : PhysicalShape prepared) (guard : ReadGuard) (member : guard ∈ readGuards prepared) :
    guard.cellId ∉ (writes prepared).map DataWrite.cellId := by
  rcases List.mem_append.mp member with source | authority
  · exact shape.2.2.2.2.1 guard source
  · exact (of_decide_eq_true (List.mem_filter.mp authority).2).1

structure AcceptedRefill [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (ingress : DecodedIngress) where
  private mk ::
  prepared : Prepared deployment profile ambient durable ingress.command
  accepted : PurseRefillReceiver.Accepted prepared ingress
  physical : PhysicalShape prepared

def admitDecodedNative [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (native : CredentialSignatureIO.NativeConfig) (ingress : DecodedIngress) :
    IO (Except Reject (AcceptedRefill deployment profile ambient durable ingress)) := do
  match prepare deployment profile ambient durable ingress.command with
  | .error reason => return .error reason
  | .ok prepared =>
    if physical : PhysicalShape prepared then
      match ← admitNative native prepared ingress with
      | .error reason => return .error reason
      | .ok accepted => return .ok ⟨prepared, accepted, physical⟩
    else return .error .physicalPreparation

variable [DecidableEq F] {ingress : DecodedIngress}

def charge (accepted : AcceptedRefill deployment profile ambient durable ingress) :
    ResourceCost.Charge
  | .incidences => 2
  | .turnBytes => ingress.bytes.length
  | .memoryTouches => (writes accepted.prepared).length + (readGuards accepted.prepared).length
  | .storageBytes => ((writes accepted.prepared).map fun write => write.canonicalPostBytes.length).sum
  | .witnessBytes => ingress.ingress.envelope.length
  | .proofWork => 2
  | .feeDebit | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

def intent (accepted : AcceptedRefill deployment profile ambient durable ingress) :
    DataIntent rootBytes where
  transactionId := transactionId deployment.domain profile.semantics ingress
  subject := some ingress.command.subject
  writes := writes accepted.prepared
  readGuards := readGuards accepted.prepared
  nullifiers := [nullifier deployment.domain profile.semantics ingress]
  exactCharge := charge accepted
  event := event deployment.domain profile.semantics ingress
  postRootsBound := accepted.physical.2.2.2.1
  guardsReadOnly := readGuards_readonly accepted.prepared accepted.physical

/-- An accepted refill writes exactly the purse and the Book, in one intent. -/
theorem intent_writes (accepted : AcceptedRefill deployment profile ambient durable ingress) :
    (intent accepted).writes.map DataWrite.cellId =
      [⟨ingress.command.task⟩, ⟨deployment.resourceBookId⟩] := rfl

/-- An accepted refill's Book leg and purse leg balance (the joint commit). -/
theorem accepted_balanced (accepted : AcceptedRefill deployment profile ambient durable ingress) :
    aggregateDelta (bookOf accepted.prepared.book) accepted.prepared.plan = 0 :=
  accepted.prepared.balanced

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

#assert_axioms command_roundtrip
#assert_axioms command_canonical
#assert_axioms ingress_roundtrip
#assert_axioms Prepared.bookPost_exact
#assert_axioms Prepared.owner
#assert_axioms Prepared.balanced
#assert_axioms Prepared.conserves
#assert_axioms Prepared.purse_before
#assert_axioms readGuards_readonly
#assert_axioms intent_writes
#assert_axioms accepted_balanced

end Minidregg.Kernel.PurseRefillReceiver
