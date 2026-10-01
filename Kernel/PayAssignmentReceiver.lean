/-
# Kernel.PayAssignmentReceiver — a subject binds the next deposit index to an account it owns

Subject `S` asks for book index `i` for Book account `A`.  The pure decision
`decideAssignment` accepts only when

1. the pay cell's tariff is valid (`assignment_requires_valid_tariff`; the
   genesis placeholder refuses every assignment),
2. `S` holds the owner grant on `A` (`assignment_requires_owner`): the
   capability the request presents is an account capability held by `S`
   whose targets are exactly `{A}` and whose governing policy is `A`'s — the
   `NativeForBirth ∧ holder = .subject owner` fact of
   `ResourceBirth.Descriptor.OwnerGrantsBound`,
3. `A` has no index yet (`alreadyAssigned`),
4. `i` is the next free index, `nextFree = (assignment support).card`
   (`indexNotNext`), and
5. book row `i` is installed (`assignment_requires_book`; `bookExhausted`).

The write is one allocation in the append-only `assignment` namespace, so an
index is bound once (`assignment_write_once`), and it never writes the clock
(`clock_untouched`).

Authorization: `S` signs a capability-mode request of kind `account`, target
`A`, verb `transfer`, presenting that owner capability, admitted under `A`'s
current law with the operation slot `authority/operation/pay-assign`.  The
signature and capability admission (holder is the signer, window, epochs,
non-revocation, `transfer ∈ verbs`) are the source checks every account
receiver uses; the owner-grant fact above is checked on the same stored
capability.  Binding a deposit address only ever adds credit to `A`, so the
authority it requires (owning `A`) is not widened by it.
-/
import Kernel.CapabilityRevocationController
import Kernel.PayCellDomain

namespace Minidregg.Kernel.PayAssignmentReceiver

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

/-- The two target forms an owner grant on `account` takes: genesis issues
`explicit {account}`; a workspace birth issues `under account` (the owner holds
the cell as a room, K-ROOM). An `under R` grant for a room `R` containing the
account is not ownership of it: it is governed by `R`'s law, not `account`'s. -/
def OwnerTargets (targets : TargetSet .account) (account : Nat) : Prop :=
  targets = .explicit {⟨account⟩} ∨ targets = .under account

instance (targets : TargetSet .account) (account : Nat) :
    Decidable (OwnerTargets targets account) := by
  unfold OwnerTargets; infer_instance

/-- The owner-grant fact: the presented account capability is held by
`subject`, targets `{account}` or `under account`, and is governed by `account`'s policy
(`ResourceBirth.AuthorityGrant.NativeForBirth` with its holder). -/
def OwnerGrant (stored : Option (StoredCapability .account)) (subject : SubjectId)
    (account : Nat) : Prop :=
  match stored with
  | none => False
  | some stored =>
      stored.head.holder = .subject subject ∧ OwnerTargets stored.head.scope.targets account ∧
        stored.head.policyId.value = account

instance (stored : Option (StoredCapability .account)) (subject : SubjectId) (account : Nat) :
    Decidable (OwnerGrant stored subject account) := by
  unfold OwnerGrant
  split <;> infer_instance

inductive Reject where
  | malformedIngress | directoryUnavailable | authorityUnavailable | payUnavailable
  | staleAuthority | stalePay
  | tariffInvalid | notOwner | alreadyAssigned | indexNotNext | bookExhausted
  | replayedMarker | validation | physicalPreparation
  | policyUnavailable | capabilityRejected | policyRejected | policyInputRange | policyCastAlias
  | signature (reason : CredentialSignatureAdmission.Reject)
  deriving DecidableEq, Repr

def decideAssignment (store : PayStore) (stored : Option (StoredCapability .account))
    (subject : SubjectId) (account index : Nat) : Except Reject Unit :=
  match tariffOf store with
  | none => .error .tariffInvalid
  | some tariff =>
      if tariff.valid then
        if OwnerGrant stored subject account then
          if accountAssigned store account then .error .alreadyAssigned
          else if index = nextFree store then
            if (bookAt store index).isSome then .ok ()
            else .error .bookExhausted
          else .error .indexNotNext
        else .error .notOwner
      else .error .tariffInvalid

/-- The one write: bind `index` to `account`. -/
def assignmentPatch (index account : Nat) : Patch PayCell.layout :=
  [.allocate .assignment index account]

/-- Everything an accepted assignment establishes. -/
theorem decideAssignment_ok (store : PayStore) (stored : Option (StoredCapability .account))
    (subject : SubjectId) (account index : Nat)
    (accepted : decideAssignment store stored subject account index = .ok ()) :
    (∃ tariff, tariffOf store = some tariff ∧ tariff.valid) ∧ OwnerGrant stored subject account ∧
      accountAssigned store account = false ∧ index = nextFree store ∧
      (bookAt store index).isSome = true := by
  unfold decideAssignment at accepted
  cases present : tariffOf store with
  | none => simp [present] at accepted
  | some tariff =>
      simp only [present] at accepted
      by_cases valid : tariff.valid
      · by_cases owner : OwnerGrant stored subject account
        · by_cases assigned : accountAssigned store account = true
          · simp [valid, owner, assigned] at accepted
          · by_cases next : index = nextFree store
            · by_cases row : (bookAt store index).isSome = true
              · exact ⟨⟨tariff, rfl, valid⟩, owner, by simpa using assigned, next, row⟩
              · rw [if_pos valid, if_pos owner, if_neg assigned, if_pos next, if_neg row] at accepted
                cases accepted
            · rw [if_pos valid, if_pos owner, if_neg assigned, if_neg next] at accepted
              cases accepted
        · simp [valid, owner] at accepted
      · simp [valid] at accepted

/-- **An assignment requires the owner grant.** -/
theorem assignment_requires_owner (store : PayStore) (stored : Option (StoredCapability .account))
    (subject : SubjectId) (account index : Nat)
    (accepted : decideAssignment store stored subject account index = .ok ()) :
    OwnerGrant stored subject account :=
  (decideAssignment_ok store stored subject account index accepted).2.1

/-- **An assignment requires an installed book row at the index.** -/
theorem assignment_requires_book (store : PayStore) (stored : Option (StoredCapability .account))
    (subject : SubjectId) (account index : Nat)
    (accepted : decideAssignment store stored subject account index = .ok ()) :
    bookAt store index ≠ none ∧ index = nextFree store := by
  obtain ⟨_, _, _, next, row⟩ := decideAssignment_ok store stored subject account index accepted
  exact ⟨by simpa [Option.isSome_iff_ne_none] using row, next⟩

/-- **No assignment under an invalid tariff** (in particular, the genesis
placeholder). -/
theorem assignment_requires_valid_tariff (store : PayStore)
    (stored : Option (StoredCapability .account)) (subject : SubjectId) (account index : Nat)
    (accepted : decideAssignment store stored subject account index = .ok ()) :
    ∃ tariff, tariffOf store = some tariff ∧ tariff.valid :=
  (decideAssignment_ok store stored subject account index accepted).1

/-- **An assigned index cannot be reassigned**: the allocation is enabled
only at an absent index (an instance of `Store.Op.allocate_enabled_fresh`). -/
theorem assignment_write_once (store : PayStore) (index account : Nat)
    (enabled : (Op.allocate (L := PayCell.layout) .assignment index account).Enabled store) :
    assignmentAt store index = none :=
  Minidregg.Theory.Store.Op.allocate_enabled_fresh store .assignment index account enabled

/-- **The assignment receiver never writes the clock.** -/
theorem clock_untouched (index account : Nat) (op : Op PayCell.layout)
    (member : op ∈ assignmentPatch index account) : op.writeAddress? ≠ some clockAddress := by
  simp only [assignmentPatch, List.mem_singleton] at member
  subst member
  simp [Op.writeAddress?, Op.address, clockAddress]

theorem clock_preserved (store : PayStore) (index account : Nat) :
    Patch.run store (assignmentPatch index account) clockAddress = store clockAddress := by
  apply Minidregg.Theory.Store.Patch.run_frame
  intro inFootprint
  simp only [Minidregg.Theory.Store.Patch.writeFootprint, List.mem_toFinset,
    List.mem_filterMap] at inFootprint
  obtain ⟨op, member, writes⟩ := inFootprint
  exact clock_untouched index account op member writes

/-! ### Concrete poles (kernel `decide` on real stores and capabilities) -/

/-- An owner capability of `holder` on `account`, as genesis issues it. -/
def ownerCapability (holder account : Nat) : StoredCapability .account :=
  ⟨{ id := ⟨41⟩, root := ⟨41⟩, parent := none, issuer := ⟨5⟩, holder := .subject ⟨holder⟩
     scope := ⟨.explicit {⟨account⟩}, {.observeAccount, .transfer, .delegateAccount}, 100000, none, ∅⟩
     notBefore := 10, notAfter := 10010, issuerEpoch := 2, policyId := ⟨account⟩,
     policyEpoch := 0, ancestors := ∅, channels := ∅ }, []⟩

/-- A pay cell with the example tariff set and one book row. -/
def oneRowStore : PayStore :=
  (genesisStore.set tariffAddress (some exampleTariff)).set (bookAddress 0)
    (some (List.replicate 32 1))

/-- Satisfiable pole: the owner of account 8 is assigned index 0. -/
theorem owner_assigned : decideAssignment oneRowStore (some (ownerCapability 8 8)) ⟨8⟩ 8 0 = .ok () := by
  decide +kernel

/-- Satisfiable pole: a workspace-born account's owner holds it `under account`. -/
theorem room_owner_assigned :
    decideAssignment oneRowStore
      (some ⟨{ (ownerCapability 8 8).head with
        scope := ⟨.under 8, {.observeAccount, .transfer, .delegateAccount}, 100000, none, ∅⟩ }, []⟩)
      ⟨8⟩ 8 0 = .ok () := by
  decide +kernel

/-- Refuting pole: a room grant `under 7` governed by room 7's law is not
ownership of account 8, even when the account was born in room 7. -/
theorem room_member_not_owner :
    decideAssignment oneRowStore
      (some ⟨{ (ownerCapability 8 8).head with
        scope := ⟨.under 7, {.observeAccount, .transfer, .delegateAccount}, 100000, none, ∅⟩,
        policyId := ⟨7⟩ }, []⟩)
      ⟨8⟩ 8 0 = .error .notOwner := by
  decide +kernel

/-- Refuting pole of `assignment_requires_owner`: subject 9 presenting
subject 8's grant on account 8 is refused. -/
theorem non_owner_refused :
    decideAssignment oneRowStore (some (ownerCapability 8 8)) ⟨9⟩ 8 0 = .error .notOwner := by
  decide +kernel

/-- Refuting pole: a grant on another account is not ownership of this one. -/
theorem other_account_refused :
    decideAssignment oneRowStore (some (ownerCapability 8 9)) ⟨8⟩ 8 0 = .error .notOwner := by
  decide +kernel

/-- Refuting pole of `assignment_requires_book`: after index 0 is taken the
one-row book is exhausted. -/
theorem book_exhausted_refused :
    decideAssignment (oneRowStore.set (assignmentAddress 0) (some (8 : Nat)))
      (some (ownerCapability 9 9)) ⟨9⟩ 9 1 = .error .bookExhausted := by
  decide +kernel

/-- Refuting pole: a second index for the same account is refused. -/
theorem second_assignment_refused :
    decideAssignment (oneRowStore.set (assignmentAddress 0) (some (8 : Nat)))
      (some (ownerCapability 8 8)) ⟨8⟩ 8 1 = .error .alreadyAssigned := by
  decide +kernel

/-- Refuting pole of `assignment_requires_valid_tariff`: the genesis
placeholder refuses even the owner of a booked row. -/
theorem genesis_tariff_refuses :
    decideAssignment (genesisStore.set (bookAddress 0) (some (List.replicate 32 1)))
      (some (ownerCapability 8 8)) ⟨8⟩ 8 0 = .error .tariffInvalid := by
  decide +kernel

/-- Refuting pole of `assignment_write_once`: allocating an assigned index is
not enabled. -/
theorem assigned_index_not_reallocatable :
    ¬ (Op.allocate (L := PayCell.layout) .assignment (0 : Nat) (9 : Nat)).Enabled
      (oneRowStore.set (assignmentAddress 0) (some (8 : Nat))) := by
  decide +kernel

/-! ## Command and ingress -/

structure Command where
  subject : SubjectId
  capability : CapabilityId
  account : Nat
  index : Nat
  nonce : Nat
  expectedAuthorityRoot : Digest
  expectedPayRoot : Digest
  deriving DecidableEq, Repr

def commandStream : StreamCodec Command :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product capabilityIdStream
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product StreamCodec.nat
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.product digestStream digestStream))))))
    (fun c => (c.subject, c.capability, c.account, c.index, c.nonce, c.expectedAuthorityRoot,
      c.expectedPayRoot))
    (fun (subject, capability, account, index, nonce, authorityRoot, payRoot) =>
      ⟨subject, capability, account, index, nonce, authorityRoot, payRoot⟩)
    (by intro c; cases c; rfl)

def commandFrame : List UInt8 := "DREGG/PAY/ASSIGN/v1".toUTF8.toList

def commandCodec : LawfulCodec Command := framed commandFrame commandStream

theorem command_roundtrip (command : Command) :
    commandCodec.decode (commandCodec.encode command) = some command :=
  commandCodec.decode_encode command

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
  framed "DREGG/PAY/ASSIGN/SIGNED/v1".toUTF8.toList ingressStream

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
      some ⟨ingress, command, framed_canonical commandFrame commandStream commandExact,
        envelope, envelopeExact⟩

def DecodedIngress.bytes (ingress : DecodedIngress) : List UInt8 :=
  ingressCodec.encode ingress.ingress

def marker (domain semantics : Digest) (command : Command) : Nat :=
  (Sp800185Cshake256.hash "DREGG.PAY.ASSIGN.IDENTITY/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
        StreamCodec.nat))).encode
      (domain, semantics, command.subject, command.nonce))).digest.value

/-! ## The effect family over the pay cell -/

structure Declaration where
  index : Nat
  account : Nat
  expectedPreRoot : Digest
  operationNullifier : Nat

def declarationStream : StreamCodec Declaration :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product digestStream StreamCodec.nat)))
    (fun d => (d.index, d.account, d.expectedPreRoot, d.operationNullifier))
    (fun (index, account, root, nullifier) => ⟨index, account, root, nullifier⟩)
    (by intro d; cases d; rfl)

def declarationCodec : LawfulCodec Declaration :=
  ResourceBirthCodec.strictCodec declarationStream.toLawful

def declaration (domain semantics : Digest) (command : Command) : Declaration :=
  ⟨command.index, command.account, command.expectedPayRoot, marker domain semantics command⟩

structure Mode {M : Materializer PayCell.layout Digest} (pre : Materialized M) (d : Declaration) : Type where
  rootExact : d.expectedPreRoot = pre.root

def effectDigest (domain semantics : Digest) (command : Command) (d : Declaration) : Digest :=
  (Sp800185Cshake256.hash "DREGG.PAY.ASSIGN.EFFECT/v1".toUTF8.toList
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
    (Sp800185Cshake256.hash "DREGG.PAY.ASSIGN.ARGS/v1".toUTF8.toList
      (commandCodec.encode command ++ bytes)).digest

def request (snapshot : Snapshot) (pay : PayCell.Cell) (semantics : Digest) (ambient : Ambient)
    (command : Command) : Request .account :=
  ((context snapshot semantics ambient command).request declarationCodec
    (effectDigest snapshot.domain semantics command) pay.root
    (marker snapshot.domain semantics command) (declaration snapshot.domain semantics command)).2

def family (snapshot : Snapshot) (pay : PayCell.Cell) (semantics : Digest) (ambient : Ambient)
    (command : Command) : SemanticEffectFamily PayCell.layout PayCell.materializer Nat where
  Declaration := Declaration
  declarationCodec := declarationCodec
  pre := pay
  request := fun d => (context snapshot semantics ambient command).request
    declarationCodec (effectDigest snapshot.domain semantics command) pay.root
    d.operationNullifier d
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun d _ => Mode pay d
  Postcondition := fun d _ post => (assignmentPatch d.index d.account).ResultAt pay.logical post
  effectDigest := effectDigest snapshot.domain semantics command
  patch := fun d _ => assignmentPatch d.index d.account
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
  pay : PayCellDomain.Loaded deployment durable.snapshot
  decided : decideAssignment pay.cell.logical
    (readCapability authority.snapshot.cell .account command.capability)
    command.subject command.account command.index = .ok ()
  candidate : Candidate (family authority.snapshot pay.cell profile.semantics ambient command)
    pay.cell (declaration authority.snapshot.domain profile.semantics command) ()
  source : CanonicalCellRegistry.LoadedPolicySource authority.snapshot.domain directory.directory
    (authority.snapshot.authState.policyAddress ⟨command.account⟩
      (authority.snapshot.authState.policyRevision ⟨command.account⟩))

def prepare {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (command : Command) : Except Reject (Prepared deployment profile ambient durable command) := do
  let directory ← requireSome .directoryUnavailable (loadDirectory durable)
  let authority ← requireSome .authorityUnavailable (loadDeployment deployment durable.snapshot)
  let pay ← requireSome .payUnavailable (PayCellDomain.load deployment durable.snapshot)
  let snapshot := authority.snapshot
  if command.expectedAuthorityRoot = snapshot.cell.root then
    if rootExact : command.expectedPayRoot = pay.cell.root then
      match decided : decideAssignment pay.cell.logical
          (readCapability snapshot.cell .account command.capability)
          command.subject command.account command.index with
      | .error reason => throw reason
      | .ok () =>
        let d := declaration snapshot.domain profile.semantics command
        if snapshot.spent d.operationNullifier = false then
          match validate PayCell.materializer pay.cell pay.cell.root
              (assignmentPatch d.index d.account) with
          | .rejected _ => throw .validation
          | .accepted validated =>
              let source ← requireSome .policyUnavailable (CanonicalCellRegistry.loadPolicySource
                snapshot.domain directory.directory
                (snapshot.authState.policyAddress ⟨command.account⟩
                  (snapshot.authState.policyRevision ⟨command.account⟩)))
              let candidate : Candidate (family snapshot pay.cell profile.semantics ambient command)
                  pay.cell d () :=
                { preStateBound := rfl
                  modeEvidence := ⟨rootExact⟩
                  validated := validated
                  postcondition := validated.resultAt }
              pure ⟨directory, authority, pay, decided, candidate, source⟩
        else throw .replayedMarker
    else throw .stalePay
  else throw .staleAuthority

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {command : Command}

def Prepared.payPost (prepared : Prepared deployment profile ambient durable command) : PayCell.Cell :=
  prepared.candidate.validated.apply

/-- A prepared assignment holds the owner grant on the stored capability the
request presents. -/
theorem Prepared.owner (prepared : Prepared deployment profile ambient durable command) :
    OwnerGrant (readCapability prepared.authority.snapshot.cell .account command.capability)
      command.subject command.account :=
  assignment_requires_owner _ _ _ _ _ prepared.decided

/-- The prepared post-cell binds exactly the requested index to the account. -/
theorem Prepared.post_binds (prepared : Prepared deployment profile ambient durable command) :
    assignmentAt prepared.payPost.logical command.index = some command.account := by
  change Minidregg.Theory.Store.Patch.run prepared.pay.cell.logical
    (assignmentPatch command.index command.account) (assignmentAddress command.index) =
      some command.account
  exact Minidregg.Theory.Store.Store.set_eq _ _ _

theorem Prepared.clock_preserved (prepared : Prepared deployment profile ambient durable command) :
    clockOf prepared.payPost.logical = clockOf prepared.pay.cell.logical :=
  PayAssignmentReceiver.clock_preserved prepared.pay.cell.logical command.index command.account

def project (prepared : Prepared deployment profile ambient durable command)
    (logical : PayStore) : Minidregg.Pred.State :=
  ⟨CanonicalRuntimeProfile.requestSlots
      (request prepared.authority.snapshot prepared.pay.cell profile.semantics ambient command) ++
    [("authority/operation/pay-assign", 1),
     ("pay/assignment/next", Int.ofNat (nextFree logical))] ++
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
    (family prepared.authority.snapshot prepared.pay.cell profile.semantics ambient command)
    (request prepared.authority.snapshot prepared.pay.cell profile.semantics ambient command)
    prepared.pay.cell
    (declaration prepared.authority.snapshot.domain profile.semantics command) ()

def authorize [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command)
    (receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot) :
    Except Reject prepared.SemanticAccepted := do
  let wanted := request prepared.authority.snapshot prepared.pay.cell profile.semantics ambient command
  let config := policyConfig prepared
  let evidence ← requireSome .notOwner
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
      (request prepared.authority.snapshot prepared.pay.cell profile.semantics ambient command)
      ingress.ingress.envelope with
  | .error reason => return .error (.signature reason)
  | .ok receipt =>
      if same : receipt.envelopeBytes = ingress.ingress.envelope then
        match authorize prepared receipt with
        | .error reason => return .error reason
        | .ok semantic => return .ok ⟨receipt, same, semantic⟩
      else return .error .capabilityRejected

/-- The exact header the subject signs over the current pay cell. -/
def signingHeader (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) :
    Except String CredentialSignedEnvelopeController.SignedHeader := do
  let some authority := loadDeployment deployment durable.snapshot
    | .error "authority unavailable"
  let some pay := PayCellDomain.load deployment durable.snapshot
    | .error "pay cell unavailable"
  (CredentialSignatureAdmission.signingHeader authority.snapshot
    (marker deployment.domain profile.semantics command)
    ⟨.account, request authority.snapshot pay.cell profile.semantics ambient command⟩).mapError
      (fun reason => s!"pay-assign signer key: {repr reason}")

/-! ## The receiver -/

def transactionId (domain semantics : Digest) (ingress : DecodedIngress) : Digest :=
  ⟨marker domain semantics ingress.command⟩

def event (domain semantics : Digest) (ingress : DecodedIngress) : StableEvent where
  codecVersion := 1
  domain := domain
  eventId := effectDigest domain semantics ingress.command
    (declaration domain semantics ingress.command)
  canonicalBytes := ingress.bytes

def nullifier (domain semantics : Digest) (ingress : DecodedIngress) : StableNullifier :=
  CredentialAuthorityReplay.nullifier domain (marker domain semantics ingress.command)

def writes (prepared : Prepared deployment profile ambient durable command) : List DataWrite :=
  [prepared.pay.write prepared.payPost]

def policyGuard (prepared : Prepared deployment profile ambient durable command) : ReadGuard :=
  ⟨⟨prepared.source.readGuard.1⟩, prepared.source.readGuard.2⟩

def readGuards (prepared : Prepared deployment profile ambient durable command) : List ReadGuard :=
  policyGuard prepared ::
    prepared.authority.readGuards.filter fun guard => guard.cellId ∉ (writes prepared).map DataWrite.cellId

def PhysicalShape (prepared : Prepared deployment profile ambient durable command) : Prop :=
  ((writes prepared).map DataWrite.cellId).Nodup ∧
    (∀ write ∈ writes prepared, write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
    (∀ write ∈ writes prepared, ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
    (policyGuard prepared).cellId ∉ (writes prepared).map DataWrite.cellId ∧
    (∀ guard ∈ readGuards prepared, guard.expectedRoot = durable.snapshot.model.roots guard.cellId)

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
  rcases List.mem_cons.mp member with rfl | authority
  · exact shape.2.2.2.1
  · simpa using (List.mem_filter.mp authority).2

structure AcceptedAssignment [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (ingress : DecodedIngress) where
  private mk ::
  prepared : Prepared deployment profile ambient durable ingress.command
  accepted : PayAssignmentReceiver.Accepted prepared ingress
  physical : PhysicalShape prepared

def admitDecodedNative [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (native : CredentialSignatureIO.NativeConfig) (ingress : DecodedIngress) :
    IO (Except Reject (AcceptedAssignment deployment profile ambient durable ingress)) := do
  match prepare deployment profile ambient durable ingress.command with
  | .error reason => return .error reason
  | .ok prepared =>
    if physical : PhysicalShape prepared then
      match ← admitNative native prepared ingress with
      | .error reason => return .error reason
      | .ok accepted => return .ok ⟨prepared, accepted, physical⟩
    else return .error .physicalPreparation

variable [DecidableEq F] {ingress : DecodedIngress}

def charge (accepted : AcceptedAssignment deployment profile ambient durable ingress) :
    ResourceCost.Charge
  | .incidences => 1
  | .turnBytes => ingress.bytes.length
  | .memoryTouches => (writes accepted.prepared).length + (readGuards accepted.prepared).length
  | .storageBytes => ((writes accepted.prepared).map fun write => write.canonicalPostBytes.length).sum
  | .witnessBytes => ingress.ingress.envelope.length
  | .proofWork => 2
  | .feeDebit | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

def intent (accepted : AcceptedAssignment deployment profile ambient durable ingress) :
    DataIntent rootBytes where
  transactionId := transactionId deployment.domain profile.semantics ingress
  subject := some ingress.command.subject
  writes := writes accepted.prepared
  readGuards := readGuards accepted.prepared
  nullifiers := [nullifier deployment.domain profile.semantics ingress]
  exactCharge := charge accepted
  event := event deployment.domain profile.semantics ingress
  postRootsBound := writes_roots_bound accepted.prepared
  guardsReadOnly := readGuards_readonly accepted.prepared accepted.physical

theorem intent_writes_pay_cell (accepted : AcceptedAssignment deployment profile ambient durable ingress) :
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

#assert_axioms decideAssignment_ok
#assert_axioms assignment_requires_owner
#assert_axioms assignment_requires_book
#assert_axioms assignment_requires_valid_tariff
#assert_axioms assignment_write_once
#assert_axioms clock_untouched
#assert_axioms clock_preserved
#assert_axioms owner_assigned
#assert_axioms non_owner_refused
#assert_axioms other_account_refused
#assert_axioms book_exhausted_refused
#assert_axioms second_assignment_refused
#assert_axioms genesis_tariff_refuses
#assert_axioms assigned_index_not_reallocatable
#assert_axioms command_roundtrip
#assert_axioms Prepared.owner
#assert_axioms Prepared.post_binds
#assert_axioms Prepared.clock_preserved

end Minidregg.Kernel.PayAssignmentReceiver
