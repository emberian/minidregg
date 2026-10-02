/-
# Kernel.JobMoneyReceiver — the signed job-money turn (COMPUTE §2.6, lane C3 K-JOB-MONEY)

One signed command (`Command`: job, action, account, amount) is one turn over
two cells, decided by `JobMoney.decideMoney`:

* the **job** (a declared object): the money edge, lowered as declared writes
  of its eight money fields, each compared at its loaded value, guarded at the
  job's exact pre-root, and admitted by the job's **installed law** evaluated
  as a write (`request/verb = 2`) by the signer, at the deployment clock, with
  the slot `Job.moneySlot` this receiver alone projects;
* the **Book**: a transfer into the job's held account — the account whose id
  is the job cell's id, registered fresh by the fund — or the payouts out of
  it (transfers to the payees, a burn of a slash's retired share into the well).

The job law is pinned: the installed law must be C1's job law at some
parameters (`JobMoney.isJobLaw`, else `notJobLaw`), a law whose management
clause lets nobody install or revoke, so it cannot be swapped for one that lets
an ordinary write move the money fields.  A refusal by the job law names the
clause (`jobRefused path`, the `LawLeaf` path).  The clock cell is read at its
exact root.

Authorization depends on the action.  Fund and claim spend an account: the
signer's capability-mode request is kind `account`, target and policy that
account, verb `transfer`, admitted under the account's law (P6's shape), and
`decideMoney` checks the owner grant on the same stored capability.  Settle spends
no one's credit and carries no amount: the request is kind `object`, target
and policy the job, verb `mutate`, admitted under the job's own law with the
money slot — anyone holding a capability on the job may close it.  The effect
digest commits to the command bytes and the decided plan, so the signature
binds the job's pre-state and every amount.  The pay cell (the tariff: the
credit asset and the slash split) and both laws' sources enter as read guards.
-/
import Kernel.CapabilityRevocationController
import Kernel.ResourceBirthController
import Kernel.PayCellDomain
import Kernel.JobMoney
import Kernel.ClockCellDomain

namespace Minidregg.Kernel.JobMoneyReceiver

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
open Minidregg.Kernel.JobMoney
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
abbrev JobCell := Materialized DeclaredEffectCell.materializer
abbrev BookCell (deployment : Deployment) (directory : Directory Nat Registry) :=
  ResourceBirthController.Concrete.ObservedCell deployment directory deployment.resourceBookId
    .resourceBook

/-! ## Command and ingress -/

/-- `action`: 1 fund · 2 claim · 3 settle (`JobMoney.fundAction` …).  For a
settle, `account` and `amount` must be 0 and `capability` is a capability on
the job; otherwise `capability` is the signer's capability on `account`.
`jobCapability` is the claimer's capability on the job (a room member's
`under ROOM` grant covers a job born in the room): a claim is admitted only if
it admits a mutation of the job by the signer (`memberCheck`); every other
action carries 0. -/
structure Command where
  subject : SubjectId
  capability : CapabilityId
  jobCapability : CapabilityId
  job : Nat
  action : Nat
  account : Nat
  amount : Nat
  nonce : Nat
  expectedAuthorityRoot : Digest
  deriving DecidableEq, Repr

def commandStream : StreamCodec Command :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product capabilityIdStream
        (StreamCodec.product capabilityIdStream
          (StreamCodec.product StreamCodec.nat
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.product StreamCodec.nat
                (StreamCodec.product StreamCodec.nat
                  (StreamCodec.product StreamCodec.nat digestStream))))))))
    (fun c => (c.subject, c.capability, c.jobCapability, c.job, c.action, c.account, c.amount,
      c.nonce, c.expectedAuthorityRoot))
    (fun (subject, capability, jobCapability, job, action, account, amount, nonce, authorityRoot) =>
      ⟨subject, capability, jobCapability, job, action, account, amount, nonce, authorityRoot⟩)
    (by intro c; cases c; rfl)

/-- v2: the command carries the claimer's `jobCapability` (room membership). -/
def commandFrame : List UInt8 := "DREGG/JOB/MONEY/v2".toUTF8.toList

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

def ingressFrame : List UInt8 := "DREGG/JOB/MONEY/SIGNED/v1".toUTF8.toList

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
  (Sp800185Cshake256.hash "DREGG.JOB.MONEY.IDENTITY/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
        StreamCodec.nat))).encode
      (domain, semantics, command.subject, command.nonce))).digest.value

/-! ## Whose authority a command spends -/

/-- Settle is authorized on the job; fund and claim on the account they burn. -/
def kindOf (command : Command) : ResourceKind :=
  if command.action = settleAction then .object else .account

def targetOf (command : Command) : Nat :=
  if command.action = settleAction then command.job else command.account

def verbOf (command : Command) : Verb (kindOf command) :=
  if settle : command.action = settleAction then
    cast (by rw [kindOf, if_pos settle]) Verb.mutateObject
  else cast (by rw [kindOf, if_neg settle]) Verb.transfer

/-! ## The effect family over the job -/

def jobStream : StreamCodec Job :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
          (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))))
    (fun j => (j.state, j.caller, j.callerAcct, j.price, j.escrow, j.provider, j.providerAcct,
      j.bond))
    (fun (state, caller, callerAcct, price, escrow, provider, providerAcct, bond) =>
      ⟨state, caller, callerAcct, price, escrow, provider, providerAcct, bond⟩)
    (by intro j; cases j; rfl)

/-- A move as `(tag, a, b, c)`: fund `(1, account, amount, 0)`, claim
`(2, provider, account, amount)`, settle `(3, provider, caller, retired)`.
The declaration codec is strict, so only canonical bytes decode. -/
def moveStream : StreamCodec Move :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat StreamCodec.nat)))
    (fun
      | .fund account amount => (1, account, amount, 0)
      | .claim provider account amount => (2, provider, account, amount)
      | .settle p => (3, p.provider, p.caller, p.retired))
    (fun (tag, a, b, c) =>
      if tag = 1 then .fund a b else if tag = 2 then .claim a b c else .settle ⟨a, b, c⟩)
    (by intro m; cases m <;> rfl)

def planStream : StreamCodec Plan :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product jobStream moveStream)))
    (fun p => (p.asset, p.job, p.before, p.move))
    (fun (asset, job, before, move) => ⟨asset, job, before, move⟩)
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

/-- The job's pre-root is the loaded one: the signed request carries it as
`preStateRoot` and the declaration carries the loaded job, so a job that moved
between the signing plan and the submission no longer matches the signed header. -/
def declaration (domain semantics : Digest) (command : Command) (jobRoot : Digest)
    (plan : Plan) : Declaration :=
  ⟨plan, jobRoot, marker domain semantics command⟩

def scalarCommand (command : Command) (d : Declaration) : DeclaredResourceScalar.Command :=
  ⟨.object, command.job, command.subject, command.capability, 1,
    d.expectedPreRoot, d.operationNullifier,
    JobMoney.actions command.job d.plan.before d.plan.after⟩

/-- The job leg's patch: the money writes, then the kernel's ratchet of the
job's blinding at the turn's height (K-HIDE-ROTATE). -/
def jobPatch (command : Command) (d : Declaration) (pre : Store effectLayout) (height : Nat) :
    Patch effectLayout :=
  DeclaredResourceScalar.cellPatch (scalarCommand command d) ++
    DeclaredEffectCell.blinding.patch pre height

structure Mode {M : Materializer effectLayout Digest} (pre : Materialized M) (d : Declaration) : Type where
  rootExact : d.expectedPreRoot = pre.root

def effectDigest (domain semantics : Digest) (command : Command) (d : Declaration) : Digest :=
  (Sp800185Cshake256.hash "DREGG.JOB.MONEY.EFFECT/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product bytesStream bytesStream))).encode
      (domain, semantics, commandCodec.encode command, declarationCodec.encode d))).digest

structure Ambient where
  federation : FederationId
  height : Height

def context (snapshot : Snapshot) (semantics : Digest) (ambient : Ambient) (command : Command) :
    RequestContext where
  authority :=
    { kind := kindOf command
      domain := snapshot.domain
      semantics := semantics
      federation := ambient.federation
      subject := command.subject
      subjectKeyEpoch := snapshot.authState.subjectKeyEpoch command.subject
      target := ⟨targetOf command⟩
      verb := verbOf command
      nonce := marker snapshot.domain semantics command
      height := ambient.height
      policyId := ⟨targetOf command⟩
      policyEpoch := snapshot.authState.policyEpoch ⟨targetOf command⟩
      policyRevision := snapshot.authState.policyRevision ⟨targetOf command⟩
      cost := (commandCodec.encode command).length }
  argsDigestBytes := fun bytes =>
    (Sp800185Cshake256.hash "DREGG.JOB.MONEY.ARGS/v1".toUTF8.toList
      (commandCodec.encode command ++ bytes)).digest

def request (snapshot : Snapshot) (job : JobCell) (semantics : Digest) (ambient : Ambient)
    (command : Command) (plan : Plan) : Request (kindOf command) :=
  ((context snapshot semantics ambient command).request declarationCodec
    (effectDigest snapshot.domain semantics command) job.root
    (marker snapshot.domain semantics command)
    (declaration snapshot.domain semantics command job.root plan)).2

/-! ## Membership: who may claim

A claim spends the claimer's account (authorized under the account's law), and
it also takes part in the job: the claimer must hold a capability that admits
a mutation of the job, the request the claim's own context makes with the job
as target (a room member's `under ROOM` grant covers every job born in the
room). The check is the authority layer's own `capabilityAdmissibleCheck`
(holder, scope through the parent chain, validity window, the job's law and
epoch, issuer, revocation), on the capability the command names. -/

/-- The claim's context with the job as the target of a mutation. -/
def memberContext (snapshot : Snapshot) (semantics : Digest) (ambient : Ambient) (command : Command) :
    RequestContext where
  authority :=
    { kind := .object
      domain := snapshot.domain
      semantics := semantics
      federation := ambient.federation
      subject := command.subject
      subjectKeyEpoch := snapshot.authState.subjectKeyEpoch command.subject
      target := ⟨command.job⟩
      verb := Verb.mutateObject
      nonce := marker snapshot.domain semantics command
      height := ambient.height
      policyId := ⟨command.job⟩
      policyEpoch := snapshot.authState.policyEpoch ⟨command.job⟩
      policyRevision := snapshot.authState.policyRevision ⟨command.job⟩
      cost := (commandCodec.encode command).length }
  argsDigestBytes := (context snapshot semantics ambient command).argsDigestBytes

def memberRequest (snapshot : Snapshot) (job : JobCell) (semantics : Digest) (ambient : Ambient)
    (command : Command) (plan : Plan) : Request .object :=
  ((memberContext snapshot semantics ambient command).request declarationCodec
    (effectDigest snapshot.domain semantics command) job.root
    (marker snapshot.domain semantics command)
    (declaration snapshot.domain semantics command job.root plan)).2

/-- A claim names a capability that admits mutating the job; any other action names none. -/
def memberCheck (snapshot : Snapshot) (job : JobCell) (semantics : Digest) (ambient : Ambient)
    (command : Command) (plan : Plan) : Bool :=
  if command.action = claimAction then
    match readCapability snapshot.cell .object command.jobCapability with
    | none => false
    | some stored =>
        AuthorizationDeclaration.capabilityAdmissibleCheck stored.head snapshot.authState
          (memberRequest snapshot job semantics ambient command plan)
  else command.jobCapability.value == 0

/-- **Only a member claims.** A claim that passes `memberCheck` names a stored
capability that is admissible for a mutation of the job by the claimer. -/
theorem memberCheck_claim {snapshot : Snapshot} {job : JobCell} {semantics : Digest}
    {ambient : Ambient} {command : Command} {plan : Plan}
    (checked : memberCheck snapshot job semantics ambient command plan = true)
    (claim : command.action = claimAction) :
    ∃ stored, readCapability snapshot.cell .object command.jobCapability = some stored ∧
      stored.head.Admissible snapshot.authState
        (memberRequest snapshot job semantics ambient command plan) := by
  unfold memberCheck at checked
  rw [if_pos claim] at checked
  split at checked
  · cases checked
  · rename_i stored found
    exact ⟨stored, found,
      (AuthorizationDeclaration.capabilityAdmissibleCheck_eq_true_iff _ _ _).mp checked⟩

def family (snapshot : Snapshot) (job : JobCell) (semantics : Digest) (ambient : Ambient)
    (command : Command) :
    SemanticEffectFamily effectLayout DeclaredEffectCell.materializer Nat where
  Declaration := Declaration
  declarationCodec := declarationCodec
  pre := job
  request := fun d => (context snapshot semantics ambient command).request
    declarationCodec (effectDigest snapshot.domain semantics command) job.root
    d.operationNullifier d
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun d _ => Mode job d
  Postcondition := fun d _ post => (jobPatch command d job.logical ambient.height).ResultAt job.logical post
  effectDigest := effectDigest snapshot.domain semantics command
  patch := fun d _ => jobPatch command d job.logical ambient.height
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

/-- The money slots this receiver projects, and nothing else does. -/
def moneySlots (command : Command) : List (String × Int) :=
  [(Minidregg.Kernel.Job.moneySlot, 1), (actionSlot, Int.ofNat command.action),
   (accountSlot, Int.ofNat command.account), (amountSlot, Int.ofNat command.amount)]

/-- The job law's view of the money edge: the money slots, a write by the
signer, the deployment clock (`clock/now`, `clock/day`: the claim edge reads
`claimBy`), then the job's exact declared projection from its loaded store to
the candidate post. -/
def jobState (command : Command) (clock : ClockCell.Clock) (pre post : Store effectLayout) :
    Minidregg.Pred.State :=
  ⟨moneySlots command ++ ("request/verb", 2) :: ("request/subject", Int.ofNat command.subject.value) ::
    ClockCell.slots clock ++ DeclaredResourceProjection.project command.job pre post⟩

/-- The job the directory holds at `job`, selected as a declared object. -/
structure LoadedJob (deployment : Deployment) (directory : Directory Nat Registry) (job : Nat) where
  packed : PackedCell Registry
  present : directory.slots job = .present packed
  cell : JobCell
  selected : CanonicalCellRegistry.selectDeclared deployment job .object packed = some cell

def loadJob (deployment : Deployment) (directory : Directory Nat Registry) (job : Nat) :
    Option (LoadedJob deployment directory job) :=
  match present : directory.slots job with
  | .absent => none
  | .present packed =>
      match selected : CanonicalCellRegistry.selectDeclared deployment job .object packed with
      | none => none
      | some cell => some ⟨packed, present, cell, selected⟩

/-! ## Preparation -/

structure Prepared {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (command : Command) where
  private mk ::
  directory : LoadedDirectory durable
  authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot
  pay : PayCellDomain.Loaded deployment durable.snapshot
  clock : ClockCellDomain.Loaded deployment durable.snapshot
  book : BookCell deployment directory.directory
  jobBefore : PackedCell Registry
  jobPresent : directory.directory.slots command.job = .present jobBefore
  job : JobCell
  jobSelected : CanonicalCellRegistry.selectDeclared deployment command.job .object jobBefore =
    some job
  plan : Plan
  decided : JobMoney.decideMoney (tariffOf pay.cell.logical)
    (readCapability authority.snapshot.cell .account command.capability) command.subject
    (bookOf book) command.job (readJob command.job job.logical)
    command.action command.account command.amount = .ok plan
  resources : CanonicalResourceKernel.AcceptedBatch book.payload plan.batch
  candidate : Candidate (family authority.snapshot job profile.semantics ambient command)
    job (declaration authority.snapshot.domain profile.semantics command job.root plan) ()
  jobLaw : CanonicalCellRegistry.LoadedPolicySource authority.snapshot.domain directory.directory
    (authority.snapshot.authState.policyAddress ⟨command.job⟩
      (authority.snapshot.authState.policyRevision ⟨command.job⟩))
  member : memberCheck authority.snapshot job profile.semantics ambient command plan = true
  jobLawPinned : JobMoney.isJobLaw jobLaw.record.predicate = true
  jobAccepted : Minidregg.Pred.eval jobLaw.record.predicate ⟨[]⟩
    (jobState command clock.clock job.logical candidate.validated.apply.logical) = true
  source : CanonicalCellRegistry.LoadedPolicySource authority.snapshot.domain directory.directory
    (authority.snapshot.authState.policyAddress ⟨targetOf command⟩
      (authority.snapshot.authState.policyRevision ⟨targetOf command⟩))

/-- The decision, in order: the loaded cells, the pinned authority root, the
pure `JobMoney.decideMoney`, the marker, the job's declared-cell checks and patch
validation, the job's installed law (pinned to C1's job law by `JobMoney.isJobLaw`, then
evaluated as the signer's write at the clock with the money slot), and the authorization
policy's source.  Refusals before the signature check are named. -/
def prepare {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (command : Command) : Except Reject (Prepared deployment profile ambient durable command) := do
  let directory ← requireSome .directoryUnavailable (loadDirectory durable)
  let authority ← requireSome .authorityUnavailable (loadDeployment deployment durable.snapshot)
  let pay ← requireSome .payUnavailable (PayCellDomain.load deployment durable.snapshot)
  let clock ← requireSome .clockUnavailable (ClockCellDomain.load deployment durable.snapshot)
  let book ← requireSome .bookUnavailable
    (ResourceBirthController.Concrete.observeCell deployment directory.directory
      deployment.resourceBookId .resourceBook)
  let loaded ← requireSome .jobUnavailable (loadJob deployment directory.directory command.job)
  let jobBefore := loaded.packed
  let present := loaded.present
  let job := loaded.cell
  let selected := loaded.selected
  let snapshot := authority.snapshot
  if command.expectedAuthorityRoot = snapshot.cell.root then
      match decided : JobMoney.decideMoney (tariffOf pay.cell.logical)
          (readCapability snapshot.cell .account command.capability) command.subject
          (bookOf book) command.job (readJob command.job job.logical)
          command.action command.account command.amount with
      | .error reason => throw reason
      | .ok plan =>
        let d := declaration snapshot.domain profile.semantics command job.root plan
        if snapshot.spent d.operationNullifier = false then
          match DeclaredResourceScalar.prepareCell snapshot profile.semantics
              ⟨ambient.federation, ambient.height⟩ job (scalarCommand command d) with
          | .error reason => throw (.jobCell reason)
          | .ok _ =>
            match validate DeclaredEffectCell.materializer job job.root
                (jobPatch command d job.logical ambient.height) with
            | .rejected _ => throw .validation
            | .accepted validated =>
              let candidate : Candidate (family snapshot job profile.semantics ambient command)
                  job d () :=
                { preStateBound := rfl
                  modeEvidence := ⟨rfl⟩
                  validated := validated
                  postcondition := validated.resultAt }
              let jobLaw ← requireSome .jobLawUnavailable
                (CanonicalCellRegistry.loadPolicySource snapshot.domain directory.directory
                  (snapshot.authState.policyAddress ⟨command.job⟩
                    (snapshot.authState.policyRevision ⟨command.job⟩)))
              if member : memberCheck snapshot job profile.semantics ambient command plan = true then
              if pinned : JobMoney.isJobLaw jobLaw.record.predicate = true then
              if jobAccepted : Minidregg.Pred.eval jobLaw.record.predicate ⟨[]⟩
                  (jobState command clock.clock job.logical candidate.validated.apply.logical) = true then
                let source ← requireSome .policyUnavailable
                  (CanonicalCellRegistry.loadPolicySource snapshot.domain directory.directory
                    (snapshot.authState.policyAddress ⟨targetOf command⟩
                      (snapshot.authState.policyRevision ⟨targetOf command⟩)))
                pure ⟨directory, authority, pay, clock, book, jobBefore, present, job, selected, plan,
                  decided,
                  CanonicalResourceKernel.AcceptedBatch.ofAdmission
                    (decideMoney_plan decided).1,
                  candidate, jobLaw, member, pinned, jobAccepted, source⟩
              else throw (.jobRefused ((Minidregg.Pred.firstFailingLeaf jobLaw.record.predicate ⟨[]⟩
                  (jobState command clock.clock job.logical candidate.validated.apply.logical)).getD []))
              else throw .notJobLaw
              else throw .notMember
        else throw .replayedMarker
  else throw .staleAuthority

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {command : Command}

def Prepared.jobPost (prepared : Prepared deployment profile ambient durable command) : JobCell :=
  prepared.candidate.validated.apply

def Prepared.bookPost (prepared : Prepared deployment profile ambient durable command) :
    Materialized (CanonicalCellRegistry.materializer .resourceBook) :=
  prepared.resources.post

/-- The prepared Book is exactly the plan's Book leg applied to the loaded Book. -/
theorem Prepared.bookPost_exact (prepared : Prepared deployment profile ambient durable command) :
    CanonicalResourceKernel.logicalBook prepared.bookPost.logical =
      prepared.plan.batch.apply (bookOf prepared.book) :=
  prepared.resources.post_logicalBook

/-- A prepared money turn's three legs balance at the credit coordinate. -/
theorem Prepared.balanced (prepared : Prepared deployment profile ambient durable command) :
    aggregateDelta (bookOf prepared.book) prepared.plan = 0 :=
  (decideMoney_plan prepared.decided).2.1

/-- A prepared money turn conserves the Book's total (well included); its
held change, circulating change and retired credit sum to zero; and the job's
held account in the committed Book holds exactly what the job cell will say. -/
theorem Prepared.conserves (prepared : Prepared deployment profile ambient durable command) :
    (CanonicalResourceKernel.logicalBook prepared.bookPost.logical).totalAsset prepared.plan.asset =
        (bookOf prepared.book).totalAsset prepared.plan.asset ∧
      (Int.ofNat prepared.plan.after.held - Int.ofNat prepared.plan.before.held) +
        (circulating (CanonicalResourceKernel.logicalBook prepared.bookPost.logical)
            prepared.plan.asset prepared.plan.job -
          circulating (bookOf prepared.book) prepared.plan.asset prepared.plan.job) +
        Int.ofNat prepared.plan.retired = 0 ∧
      (CanonicalResourceKernel.logicalBook prepared.bookPost.logical).balance prepared.plan.job
          prepared.plan.asset = Int.ofNat prepared.plan.after.held := by
  rw [prepared.bookPost_exact]
  exact ⟨(escrow_conserved prepared.decided).1, (escrow_conserved prepared.decided).2.1,
    held_agrees prepared.decided⟩

/-- An accepted claim's claimer holds a capability admissible for mutating the job. -/
theorem Prepared.claim_by_member (prepared : Prepared deployment profile ambient durable command)
    (claim : command.action = claimAction) :
    ∃ stored, readCapability prepared.authority.snapshot.cell .object command.jobCapability =
        some stored ∧
      stored.head.Admissible prepared.authority.snapshot.authState
        (memberRequest prepared.authority.snapshot prepared.job profile.semantics ambient command
          prepared.plan) :=
  memberCheck_claim prepared.member claim

/-- The money leg starts from the job the Store holds. -/
theorem Prepared.job_before (prepared : Prepared deployment profile ambient durable command) :
    readJob command.job prepared.job.logical = some prepared.plan.before := by
  obtain ⟨t, j, -, -, -, same, -, -, before, -⟩ := decideMoney_ok prepared.decided
  rw [same, before]

def project (prepared : Prepared deployment profile ambient durable command)
    (logical : Store effectLayout) : Minidregg.Pred.State :=
  ⟨WorldKindLawDependencies.targetSelectorSlots prepared.directory.directory (targetOf command) ++
    CanonicalRuntimeProfile.requestSlots
      (request prepared.authority.snapshot prepared.job profile.semantics ambient command
        prepared.plan) ++
    moneySlots command ++ [("job/money/job", Int.ofNat command.job)] ++
    ClockCell.slots prepared.clock.clock ++
    DeclaredResourceProjection.project command.job prepared.job.logical logical ++
    DeclaredResourceController.bytesSlots "command/bytes" 0 (commandCodec.encode command) ++
    ResourceAuthorityProjection.grantSlots "authority/owner" (kindOf command) command.capability
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
  WorldKindLawDependencies.loadTarget deployment prepared.directory.directory (targetOf command)

def policyConfig [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command) : ComposedPolicyAdmission.Config F :=
  PhysicalLawResolution.config profile.compilerProfile prepared.authority.snapshot
    prepared.directory.directory
    (sourceCapabilityPortal prepared.authority.snapshot
      (marker prepared.authority.snapshot.domain profile.semantics command))
    (step prepared) (targetOf command)
    ((kindDependencies prepared).map (·.additional) |>.getD [])

/-- Money authorization and the changed resource's restrictions are separate
obligations. A neutral job/purse cannot discard its room or kind exports. -/
def effectLaw (prepared : Prepared deployment profile ambient durable command) :
    Option (Minidregg.Pred.Pred × List (Nat × Digest)) := do
  let structural ← WorldKindLawDependencies.loadTarget deployment prepared.directory.directory command.job
  let loaded ← PhysicalLawResolution.loadTarget prepared.authority.snapshot
    prepared.directory.directory profile.semantics command.job
    PhysicalLawResolution.resolutionBudget structural.additional
  pure (ResolvedLawCompilation.predicate loaded.graph.resolved,
    loaded.sourceGuards ++ structural.readGuards)

/-- This is the actual object mutation view, not the account transfer header.
The receiver supplies all selector/header coordinates before payload slots. -/
def effectProject (prepared : Prepared deployment profile ambient durable command)
    (logical : Store effectLayout) : Minidregg.Pred.State :=
  ⟨WorldKindLawDependencies.targetSelectorSlots prepared.directory.directory command.job ++
    [("request/kind", Int.ofNat (CanonicalRuntimeProfile.requestKindTag .object)),
     ("request/verb", Int.ofNat (verbTag .mutateObject)),
     ("request/target", Int.ofNat command.job),
     ("target/policyId", Int.ofNat command.job),
     ("request/policyEpoch", Int.ofNat (prepared.authority.snapshot.authState.policyEpoch ⟨command.job⟩)),
     ("request/policyRevision", Int.ofNat (prepared.authority.snapshot.authState.policyRevision ⟨command.job⟩))] ++
    (jobState command prepared.clock.clock prepared.job.logical logical).slots ++ (project prepared logical).slots⟩

def effectLawAccepted (prepared : Prepared deployment profile ambient durable command) : Bool :=
  match effectLaw prepared with
  | none => false
  | some (predicate, _) => Minidregg.Pred.eval predicate
      (effectProject prepared prepared.job.logical)
      (effectProject prepared prepared.candidate.validated.apply.logical)

def lawReadGuards (prepared : Prepared deployment profile ambient durable command) :
    Option (List (Nat × Digest)) := do
  let structural ← kindDependencies prepared
  let sources ← PhysicalLawResolution.readGuards prepared.authority.snapshot
    prepared.directory.directory profile.semantics (targetOf command) structural.additional
  let effect ← effectLaw prepared
  pure (sources ++ structural.readGuards ++ effect.2)

abbrev Prepared.SemanticAccepted [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command) :=
  AcceptedCellEffect (portal := (policyConfig prepared).portal)
    (authState := prepared.authority.snapshot.authState)
    (family prepared.authority.snapshot prepared.job profile.semantics ambient command)
    (request prepared.authority.snapshot prepared.job profile.semantics ambient command
      prepared.plan)
    prepared.job
    (declaration prepared.authority.snapshot.domain profile.semantics command prepared.job.root
      prepared.plan) ()

def authorize [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command)
    (receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot) :
    Except Reject prepared.SemanticAccepted := do
  let wanted := request prepared.authority.snapshot prepared.job profile.semantics ambient
    command prepared.plan
  let config := policyConfig prepared
  let _ ← requireSome .policyUnavailable (kindDependencies prepared)
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
      (request prepared.authority.snapshot prepared.job profile.semantics ambient command
        prepared.plan)
      ingress.ingress.envelope with
  | .error reason => return .error (.signature reason)
  | .ok receipt =>
      if same : receipt.envelopeBytes = ingress.ingress.envelope then
        match authorize prepared receipt with
        | .error reason => return .error reason
        | .ok semantic => return .ok ⟨receipt, same, semantic⟩
      else return .error .capabilityRejected

/-- The exact header the signer signs.  It discloses no decision: when the
command does not decide, it is built over a plan that echoes the command at the
loaded job (and submission then refuses with the named reason). -/
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
  let .present jobBefore := directory.directory.slots command.job
    | .error "job unavailable"
  let some job := CanonicalCellRegistry.selectDeclared deployment command.job .object jobBefore
    | .error "job unavailable"
  let before := (readJob command.job job.logical).getD ⟨0, 0, 0, 0, 0, 0, 0, 0⟩
  let plan : Plan :=
    match JobMoney.decideMoney (tariffOf pay.cell.logical)
        (readCapability authority.snapshot.cell .account command.capability) command.subject
        (bookOf book) command.job (readJob command.job job.logical)
        command.action command.account command.amount with
    | .ok plan => plan
    | .error _ => ⟨((tariffOf pay.cell.logical).map Tariff.asset).getD 0, command.job, before,
        .fund command.account command.amount⟩
  (CredentialSignatureAdmission.signingHeader authority.snapshot
    (marker deployment.domain profile.semantics command)
    ⟨kindOf command, request authority.snapshot job profile.semantics ambient command plan⟩).mapError
      (fun reason => s!"job-money signer key: {repr reason}")

/-! ## The receiver -/

def transactionId (domain semantics : Digest) (ingress : DecodedIngress) : Digest :=
  ⟨marker domain semantics ingress.command⟩

def event (domain _semantics : Digest) (ingress : DecodedIngress) : StableEvent where
  codecVersion := 1
  domain := domain
  eventId := (Sp800185Cshake256.hash "DREGG.JOB.MONEY.EVENT/v1".toUTF8.toList
    ingress.bytes).digest
  canonicalBytes := ingress.bytes

def nullifier (domain semantics : Digest) (ingress : DecodedIngress) : StableNullifier :=
  CredentialAuthorityReplay.nullifier domain (marker domain semantics ingress.command)

def jobWrite (prepared : Prepared deployment profile ambient durable command) : DataWrite :=
  ResourceBirthController.Concrete.packedWrite command.job prepared.jobBefore
    (DeclaredResourceScalar.packDeclared .object prepared.jobPost)

def bookWrite (prepared : Prepared deployment profile ambient durable command) : DataWrite :=
  ResourceBirthController.Concrete.packedWrite deployment.resourceBookId
    ⟨.resourceBook, prepared.book.payload⟩ ⟨.resourceBook, prepared.bookPost⟩

def writes (prepared : Prepared deployment profile ambient durable command) : List DataWrite :=
  [jobWrite prepared, bookWrite prepared]

def policyGuard (prepared : Prepared deployment profile ambient durable command) : ReadGuard :=
  ⟨⟨prepared.source.readGuard.1⟩, prepared.source.readGuard.2⟩

def jobLawGuard (prepared : Prepared deployment profile ambient durable command) : ReadGuard :=
  ⟨⟨prepared.jobLaw.readGuard.1⟩, prepared.jobLaw.readGuard.2⟩

/-- The tariff (the credit asset and the slash split) is read at the pay cell's exact root. -/
def payGuard (prepared : Prepared deployment profile ambient durable command) : ReadGuard :=
  ⟨PayCellDomain.cellIdOf deployment, PayCellDomain.cellRoot prepared.pay.cell⟩

/-- The clock the job law read (`claimBy`) is read at the clock cell's exact root. -/
def clockGuard (prepared : Prepared deployment profile ambient durable command) : ReadGuard :=
  ⟨ClockCellDomain.cellIdOf deployment, ClockCellDomain.cellRoot prepared.clock.cell⟩

def sourceGuards (prepared : Prepared deployment profile ambient durable command) : List ReadGuard :=
  [policyGuard prepared, jobLawGuard prepared, payGuard prepared, clockGuard prepared].dedup

def readGuards (prepared : Prepared deployment profile ambient durable command) : List ReadGuard :=
  sourceGuards prepared ++
    (prepared.authority.readGuards ++
      ((lawReadGuards prepared).getD []).map (fun (cellIdValue, root) => (⟨⟨cellIdValue⟩, root⟩ : Minidregg.Kernel.DurableDataIntent.ReadGuard))).filter fun guard =>
      guard.cellId ∉ (writes prepared).map DataWrite.cellId ∧
        guard.cellId ∉ (sourceGuards prepared).map ReadGuard.cellId

def PhysicalShape (prepared : Prepared deployment profile ambient durable command) : Prop :=
  ((writes prepared).map DataWrite.cellId).Nodup ∧
    (∀ write ∈ writes prepared, write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
    (∀ write ∈ writes prepared, ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
    (∀ write ∈ writes prepared, rootBytes write.canonicalPostBytes = write.exactPost) ∧
    (∀ guard ∈ sourceGuards prepared, guard.cellId ∉ (writes prepared).map DataWrite.cellId) ∧
    (∀ guard ∈ readGuards prepared, guard.expectedRoot = durable.snapshot.model.roots guard.cellId) ∧
    (lawReadGuards prepared).isSome = true ∧
    effectLawAccepted prepared = true

/-- A successful account grant cannot bypass a refusing law on the actual
job/purse effect. This is a required receiving proposition before intent creation. -/
theorem effect_refusal_blocks_physical
    (prepared : Prepared deployment profile ambient durable command)
    (refused : effectLawAccepted prepared = false) : ¬ PhysicalShape prepared := by
  intro shape
  rcases shape with ⟨_, _, _, _, _, _, _, admitted⟩
  rw [refused] at admitted
  cases admitted

/-- Missing current/pinned law material is a refusal, not an empty guard set. -/
theorem unavailable_law_blocks_physical
    (prepared : Prepared deployment profile ambient durable command)
    (missing : lawReadGuards prepared = none) : ¬ PhysicalShape prepared := by
  intro shape
  rcases shape with ⟨_, _, _, _, _, _, present, _⟩
  simp [missing] at present

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

structure AcceptedMoney [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (ingress : DecodedIngress) where
  private mk ::
  prepared : Prepared deployment profile ambient durable ingress.command
  accepted : JobMoneyReceiver.Accepted prepared ingress
  physical : PhysicalShape prepared

def admitDecodedNative [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (native : CredentialSignatureIO.NativeConfig) (ingress : DecodedIngress) :
    IO (Except Reject (AcceptedMoney deployment profile ambient durable ingress)) := do
  match prepare deployment profile ambient durable ingress.command with
  | .error reason => return .error reason
  | .ok prepared =>
    if physical : PhysicalShape prepared then
      match ← admitNative native prepared ingress with
      | .error reason => return .error reason
      | .ok accepted => return .ok ⟨prepared, accepted, physical⟩
    else return .error .physicalPreparation

variable [DecidableEq F] {ingress : DecodedIngress}

def charge (accepted : AcceptedMoney deployment profile ambient durable ingress) :
    ResourceCost.Charge
  | .incidences => 2
  | .turnBytes => ingress.bytes.length
  | .memoryTouches => (writes accepted.prepared).length + (readGuards accepted.prepared).length
  | .storageBytes => ((writes accepted.prepared).map fun write => write.canonicalPostBytes.length).sum
  | .witnessBytes => ingress.ingress.envelope.length
  | .proofWork => 2
  | .feeDebit | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

def intent (accepted : AcceptedMoney deployment profile ambient durable ingress) :
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

/-- An accepted money turn writes exactly the job and the Book, in one intent. -/
theorem intent_writes (accepted : AcceptedMoney deployment profile ambient durable ingress) :
    (intent accepted).writes.map DataWrite.cellId =
      [⟨ingress.command.job⟩, ⟨deployment.resourceBookId⟩] := rfl

/-- An accepted money turn's legs balance (the joint commit). -/
theorem accepted_balanced (accepted : AcceptedMoney deployment profile ambient durable ingress) :
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
#assert_axioms Prepared.balanced
#assert_axioms Prepared.conserves
#assert_axioms Prepared.job_before
#assert_axioms memberCheck_claim
#assert_axioms Prepared.claim_by_member
#assert_axioms readGuards_readonly
#assert_axioms intent_writes
#assert_axioms accepted_balanced

end Minidregg.Kernel.JobMoneyReceiver
