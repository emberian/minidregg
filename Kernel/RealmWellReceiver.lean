/-
# Kernel.RealmWellReceiver — realm wells: mint and burn under the well's law (K-WELL)

A **realm well** is an account born in a realm: its cell id is the asset
(`CanonicalResourceKernel`: an asset is named by its issuer-well account), its
realm is its row in the authority cell's append-only `parent` plane, and its
law is its own governing policy. Nothing here stores those three facts again.

One signed command `{well, op, account, amount}` is one Book batch with one
operation (`Compiler.RealmWellCodec`):

* **mint** `Operation.mint well account amount`: the request targets the well
  with verb `mintAsset`, so the subject must hold a capability covering the well
  with that verb (the founder's owner grant, or a child delegated from it — the
  referee's grant), AND the well's law must admit the projected request
  (`well_mint_requires_grant_and_law`);
* **burn** `Operation.burn account well amount`: the request targets the
  debited account with verb `burnAsset` under that account's law, so only the
  holder (or whoever the holder delegated `burnAsset` to) destroys value; the
  Book admission requires the balance (`well_burn_requires_balance`).

The pure decision `decideWell` refuses, in order: the credit asset
(`creditWell` — credit buys, never mints: `credit_well_untouched`), a well with
no realm (`notRealmWell`), the well as its own counterparty (`accountIsWell`),
a zero amount (`zeroAmount`) and any batch the Book refuses (`bookRefused`).

Audit: every admitted batch conserves every asset (`realm_conservation`), and
over an accepted log the well's negation moves by exactly the minted minus the
burned amount (`well_tracks_mints`), so on a well born at zero,
`−well = Σ minted − Σ burned = Σ holders` (`Book.holders_sum_eq_neg_well`).
-/
import Kernel.CapabilityRevocationController
import Kernel.ResourceBirthController
import Compiler.RealmWellCodec

namespace Minidregg.Kernel.RealmWellReceiver

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.CredentialAuthorityEntryCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.RealmWellCodec
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialAuthorityEffects
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.PolicyInstall
open Minidregg.Theory.Store (Store Patch Op Address)
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CanonicalResourceKernel (Book Operation Batch AccountId AssetId)

set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev Snapshot := CredentialAuthorityDomain.Snapshot
abbrev BookCell (deployment : Deployment) (directory : Directory Nat Registry) :=
  ResourceBirthController.Concrete.ObservedCell deployment directory deployment.resourceBookId
    .resourceBook

/-! ## The pure decision -/

/-- What an admitted command decided: the asset (= its well), the realm the
well was born in, and the one posting. -/
structure Plan where
  asset : AssetId
  realm : Nat
  op : WellOp
  account : AccountId
  amount : Nat
  deriving DecidableEq, Repr

def Plan.operation (plan : Plan) : Operation :=
  match plan.op with
  | .mint => .mint plan.asset plan.account plan.amount
  | .burn => .burn plan.account plan.asset plan.amount

def Plan.batch (plan : Plan) : Batch := ⟨[], [plan.operation]⟩

@[simp] theorem Plan.operation_asset (plan : Plan) : plan.operation.posting.asset = plan.asset := by
  cases plan with
  | mk asset realm op account amount => cases op <;> rfl

theorem Plan.batch_apply (plan : Plan) (book : Book) :
    plan.batch.apply book = plan.operation.apply book := rfl

inductive Reject where
  | malformedIngress | directoryUnavailable | authorityUnavailable | bookUnavailable
  | creditWell | notRealmWell | accountIsWell | zeroAmount | bookRefused
  | replayedMarker | physicalPreparation
  | policyUnavailable | noGrant | lawRefused | policyInputRange | policyCastAlias
  | signature (reason : CredentialSignatureAdmission.Reject)
  deriving DecidableEq, Repr

/-- The decision over the loaded Book, the authority's parent map (the realm of
each cell) and the deployment's credit asset. -/
def decideWell (book : Book) (realmOf : Nat → Option Nat) (credit : AssetId) (command : Command) :
    Except Reject Plan :=
  if command.well = credit then .error .creditWell
  else match realmOf command.well with
    | none => .error .notRealmWell
    | some realm =>
      if command.account = command.well then .error .accountIsWell
      else if command.amount = 0 then .error .zeroAmount
      else if (Plan.batch ⟨command.well, realm, command.op, command.account, command.amount⟩).Admission
          book then
        .ok ⟨command.well, realm, command.op, command.account, command.amount⟩
      else .error .bookRefused

/-- Everything an admitted command decided, in one statement. -/
theorem decideWell_ok {book : Book} {realmOf : Nat → Option Nat} {credit : AssetId}
    {command : Command} {plan : Plan}
    (accepted : decideWell book realmOf credit command = .ok plan) :
    command.well ≠ credit ∧ command.account ≠ command.well ∧ 0 < command.amount ∧
      ∃ realm, realmOf command.well = some realm ∧
        plan = ⟨command.well, realm, command.op, command.account, command.amount⟩ ∧
        plan.batch.Admission book := by
  unfold decideWell at accepted
  by_cases credited : command.well = credit
  · rw [if_pos credited] at accepted; cases accepted
  · rw [if_neg credited] at accepted
    cases realm : realmOf command.well with
    | none => rw [realm] at accepted; cases accepted
    | some r =>
      rw [realm] at accepted
      simp only at accepted
      by_cases same : command.account = command.well
      · rw [if_pos same] at accepted; cases accepted
      · rw [if_neg same] at accepted
        by_cases zero : command.amount = 0
        · rw [if_pos zero] at accepted; cases accepted
        · rw [if_neg zero] at accepted
          split at accepted
          · rename_i admitted
            cases accepted
            exact ⟨credited, same, Nat.pos_of_ne_zero zero, r, rfl, rfl, admitted⟩
          · cases accepted

/-- **Credit buys, never mints.** An admitted realm command never moves any
balance of the credit asset — not its well, not any holder. -/
theorem credit_well_untouched {book : Book} {realmOf : Nat → Option Nat} {credit : AssetId}
    {command : Command} {plan : Plan}
    (accepted : decideWell book realmOf credit command = .ok plan) (holder : AccountId) :
    (plan.batch.apply book).balance holder credit = book.balance holder credit := by
  obtain ⟨notCredit, -, -, realm, -, rfl, -⟩ := decideWell_ok accepted
  rw [Plan.batch_apply]
  exact CanonicalResourceKernel.Operation.apply_balance_other_asset _ book holder credit
    (by simpa using notCredit)

/-- **A burn requires the balance**: the debited holder held at least the
burned amount of the well's asset before the burn. -/
theorem well_burn_requires_balance {book : Book} {realmOf : Nat → Option Nat} {credit : AssetId}
    {command : Command} {plan : Plan}
    (accepted : decideWell book realmOf credit command = .ok plan) (burn : command.op = .burn) :
    Int.ofNat command.amount ≤ book.balance command.account command.well := by
  obtain ⟨-, -, -, realm, -, rfl, admitted⟩ := decideWell_ok accepted
  have single := (CanonicalResourceKernel.Batch.single_admission _ book).mp admitted
  have solvent := single.sourceSolvent
  simp only [Plan.operation, burn, CanonicalResourceKernel.Operation.isIssuerMint,
    CanonicalResourceKernel.Operation.posting] at solvent
  simpa using solvent

/-- The one posting of a decided plan, applied to the Book. -/
theorem decided_apply {book : Book} {realmOf : Nat → Option Nat} {credit : AssetId}
    {command : Command} {plan : Plan}
    (accepted : decideWell book realmOf credit command = .ok plan) :
    plan.batch.apply book = plan.operation.apply book ∧ plan.asset = command.well ∧
      plan.account = command.account ∧ plan.amount = command.amount ∧ plan.op = command.op := by
  obtain ⟨-, -, -, realm, -, rfl, -⟩ := decideWell_ok accepted
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## The audit identity over an accepted log -/

/-- A log of admitted realm commands, threaded through the Book. -/
inductive AcceptedLog : Book → List Plan → Book → Prop
  | nil (book : Book) : AcceptedLog book [] book
  | cons {book final : Book} {plan : Plan} {rest : List Plan}
      (distinct : plan.account ≠ plan.asset)
      (admitted : plan.batch.Admission book)
      (tail : AcceptedLog (plan.batch.apply book) rest final) :
      AcceptedLog book (plan :: rest) final

def minted (asset : AssetId) : List Plan → Int
  | [] => 0
  | plan :: rest =>
      (if plan.asset = asset ∧ plan.op = .mint then Int.ofNat plan.amount else 0) + minted asset rest

def burned (asset : AssetId) : List Plan → Int
  | [] => 0
  | plan :: rest =>
      (if plan.asset = asset ∧ plan.op = .burn then Int.ofNat plan.amount else 0) + burned asset rest

/-- One step of the well: a mint lowers it by the amount, a burn raises it,
any other asset's plan leaves it. -/
theorem well_step (plan : Plan) (distinct : plan.account ≠ plan.asset) (book : Book)
    (asset : AssetId) :
    -((plan.batch.apply book).balance asset asset) =
      -(book.balance asset asset) +
        (if plan.asset = asset ∧ plan.op = .mint then Int.ofNat plan.amount else 0) -
        (if plan.asset = asset ∧ plan.op = .burn then Int.ofNat plan.amount else 0) := by
  change -((plan.operation.apply book).balance asset asset) = _
  by_cases same : plan.asset = asset
  · subst same
    cases op : plan.op with
    | mint =>
      simp only [Plan.operation, op]
      rw [CanonicalResourceKernel.mint_debits_issuer book plan.asset plan.account plan.amount
        (Ne.symm distinct)]
      simp [sub_eq_add_neg]
      ring
    | burn =>
      simp only [Plan.operation, op]
      rw [CanonicalResourceKernel.burn_returns_to_issuer book plan.account plan.asset plan.amount
        (Ne.symm distinct)]
      simp [sub_eq_add_neg]
      ring
  · rw [CanonicalResourceKernel.Operation.apply_balance_other_asset _ book asset asset
      (by simpa using same)]
    simp [same]

/-- **The audit identity**: over any accepted log of realm commands, the
negated well moves by exactly the minted minus the burned amount. On a well born
at zero this is `−well = Σ minted − Σ burned` (P3's `well_tracks_observed`
shape, per realm asset). -/
theorem well_tracks_mints {initial final : Book} {log : List Plan}
    (accepted : AcceptedLog initial log final) (asset : AssetId) :
    -(final.balance asset asset) =
      -(initial.balance asset asset) + minted asset log - burned asset log := by
  induction accepted with
  | nil book => simp [minted, burned]
  | @cons book final plan rest distinct admitted tail ih =>
    rw [ih, well_step plan distinct book asset]
    simp only [minted, burned]
    ring

/-- **Realm conservation**: every accepted log preserves every asset's total
(the well included). Instance of `Batch.conservation`. -/
theorem realm_conservation {initial final : Book} {log : List Plan}
    (accepted : AcceptedLog initial log final) (asset : AssetId) :
    final.totalAsset asset = initial.totalAsset asset := by
  induction accepted with
  | nil book => rfl
  | cons distinct admitted tail ih =>
    exact ih.trans (CanonicalResourceKernel.Batch.conservation _ _ admitted asset)

/-- Accounts are never removed by a realm command. -/
theorem accounts_stable {initial final : Book} {log : List Plan}
    (accepted : AcceptedLog initial log final) : final.accounts = initial.accounts := by
  induction accepted with
  | nil book => rfl
  | @cons book final plan rest distinct admitted tail ih =>
    rw [ih, Plan.batch_apply]
    exact CanonicalResourceKernel.Operation.apply_accounts _ _

/-- With the total at zero (as at genesis and at every birth), the holders of
a realm asset hold exactly the negated well after any accepted log. -/
theorem realm_holders_eq_neg_well {initial final : Book} {log : List Plan}
    (accepted : AcceptedLog initial log final) (asset : AssetId)
    (present : asset ∈ initial.accounts) (zero : initial.totalAsset asset = 0) :
    ∑ account ∈ final.accounts.erase asset, final.balance account asset =
      -(final.balance asset asset) :=
  final.holders_sum_eq_neg_well asset (by rw [accounts_stable accepted]; exact present)
    ((realm_conservation accepted asset).trans zero)

theorem AcceptedLog.snoc {initial book : Book} {log : List Plan} {plan : Plan}
    (prior : AcceptedLog initial log book) (distinct : plan.account ≠ plan.asset)
    (admitted : plan.batch.Admission book) :
    AcceptedLog initial (log ++ [plan]) (plan.batch.apply book) := by
  induction prior with
  | nil book => exact .cons distinct admitted (.nil _)
  | cons d a tail ih => exact .cons d a (ih admitted)

/-- Every admitted command extends the accepted log: the receiver's decision is
exactly a log step. -/
theorem decided_extends_log {initial book : Book} {log : List Plan}
    {realmOf : Nat → Option Nat} {credit : AssetId} {command : Command} {plan : Plan}
    (prior : AcceptedLog initial log book)
    (accepted : decideWell book realmOf credit command = .ok plan) :
    AcceptedLog initial (log ++ [plan]) (plan.batch.apply book) := by
  obtain ⟨-, distinct, -, realm, -, rfl, admitted⟩ := decideWell_ok accepted
  exact prior.snoc distinct admitted

/-! ### Concrete poles (kernel `decide` on a real Book) -/

/-- Credit well 0, realm well 5 (born in room 3), holder 7, unrelated 9. -/
def poleBook : Book where
  accounts := {0, 5, 7, 9}
  balances := DFinsupp.single (0, 0) (-10) + DFinsupp.single (7, 0) 10
  leaseRecords := 0

def poleRealm : Nat → Option Nat
  | 5 => some 3
  | _ => none

def poleCommand (well : Nat) (op : WellOp) (account amount : Nat) : Command :=
  ⟨⟨2⟩, ⟨40⟩, well, op, account, amount, 1⟩

theorem pole_mint_admitted :
    decideWell poleBook poleRealm 0 (poleCommand 5 .mint 7 20) = .ok ⟨5, 3, .mint, 7, 20⟩ := by
  decide +kernel

theorem pole_mint_then_burn_admitted :
    decideWell ((Plan.batch ⟨5, 3, .mint, 7, 20⟩).apply poleBook) poleRealm 0
      (poleCommand 5 .burn 7 5) = .ok ⟨5, 3, .burn, 7, 5⟩ := by
  decide +kernel

/-- Refuting pole of `well_burn_requires_balance`. -/
theorem pole_overburn_refused :
    decideWell ((Plan.batch ⟨5, 3, .mint, 7, 20⟩).apply poleBook) poleRealm 0
      (poleCommand 5 .burn 7 21) = .error .bookRefused := by
  decide +kernel

/-- Refuting pole of `credit_well_untouched`: the credit asset is never a realm well. -/
theorem pole_credit_refused :
    decideWell poleBook poleRealm 0 (poleCommand 0 .mint 7 1) = .error .creditWell := by
  decide +kernel

theorem pole_rootless_refused :
    decideWell poleBook poleRealm 0 (poleCommand 9 .mint 7 1) = .error .notRealmWell := by
  decide +kernel

theorem pole_self_refused :
    decideWell poleBook poleRealm 0 (poleCommand 5 .mint 5 1) = .error .accountIsWell := by
  decide +kernel

theorem pole_zero_refused :
    decideWell poleBook poleRealm 0 (poleCommand 5 .mint 7 0) = .error .zeroAmount := by
  decide +kernel

/-- A mint to an unregistered account is refused by the Book itself. -/
theorem pole_unregistered_refused :
    decideWell poleBook poleRealm 0 (poleCommand 5 .mint 8 1) = .error .bookRefused := by
  decide +kernel

/-- The audit identity on the pole log: mint 20, burn 5 leaves the well at −15. -/
theorem pole_log_tracks :
    ((Plan.batch ⟨5, 3, .burn, 7, 5⟩).apply ((Plan.batch ⟨5, 3, .mint, 7, 20⟩).apply poleBook)).balance
      5 5 = -15 ∧
    ((Plan.batch ⟨5, 3, .burn, 7, 5⟩).apply ((Plan.batch ⟨5, 3, .mint, 7, 20⟩).apply poleBook)).balance
      7 0 = 10 := by
  decide +kernel

/-! ## Command identity and the effect family over the Book -/

structure Ambient where
  federation : FederationId
  height : Height
  /-- The deployment's credit asset (`CreationTariff.asset`): never a realm well. -/
  credit : AssetId

def marker (domain semantics : Digest) (command : Command) : Nat :=
  (Sp800185Cshake256.hash "DREGG.WELL.IDENTITY/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
        StreamCodec.nat))).encode
      (domain, semantics, command.subject, command.nonce))).digest.value

structure Declaration where
  well : Nat
  op : WellOp
  account : Nat
  amount : Nat
  operationNullifier : Nat

def declarationStream : StreamCodec Declaration :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product wellOpStream
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat StreamCodec.nat))))
    (fun d => (d.well, d.op, d.account, d.amount, d.operationNullifier))
    (fun (well, op, account, amount, nullifier) => ⟨well, op, account, amount, nullifier⟩)
    (by intro d; cases d; rfl)

def declarationCodec : LawfulCodec Declaration :=
  ResourceBirthCodec.strictCodec declarationStream.toLawful

def declaration (domain semantics : Digest) (command : Command) : Declaration :=
  ⟨command.well, command.op, command.account, command.amount, marker domain semantics command⟩

def effectDigest (domain semantics : Digest) (command : Command) (d : Declaration) : Digest :=
  (Sp800185Cshake256.hash "DREGG.WELL.EFFECT/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product bytesStream bytesStream))).encode
      (domain, semantics, commandCodec.encode command, declarationCodec.encode d))).digest

/-- The request: kind account, target the well (mint) or the debited account
(burn), the matching verb, and the TARGET's own law. -/
def context (snapshot : Snapshot) (semantics : Digest) (ambient : Ambient) (command : Command) :
    RequestContext where
  authority :=
    { kind := .account
      domain := snapshot.domain
      semantics := semantics
      federation := ambient.federation
      subject := command.subject
      subjectKeyEpoch := snapshot.authState.subjectKeyEpoch command.subject
      target := ⟨command.target⟩
      verb := command.verb
      nonce := marker snapshot.domain semantics command
      height := ambient.height
      policyId := ⟨command.target⟩
      policyEpoch := snapshot.authState.policyEpoch ⟨command.target⟩
      policyRevision := snapshot.authState.policyRevision ⟨command.target⟩
      cost := (commandCodec.encode command).length }
  argsDigestBytes := fun bytes =>
    (Sp800185Cshake256.hash "DREGG.WELL.ARGS/v1".toUTF8.toList
      (commandCodec.encode command ++ bytes)).digest

abbrev BookMaterialized := Materialized (CanonicalCellRegistry.materializer .resourceBook)

def request (snapshot : Snapshot) (book : BookMaterialized) (semantics : Digest)
    (ambient : Ambient) (command : Command) : Request .account :=
  ((context snapshot semantics ambient command).request declarationCodec
    (effectDigest snapshot.domain semantics command) book.root
    (marker snapshot.domain semantics command) (declaration snapshot.domain semantics command)).2

theorem request_target (snapshot : Snapshot) (book : BookMaterialized) (semantics : Digest)
    (ambient : Ambient) (command : Command) :
    (request snapshot book semantics ambient command).target = ⟨command.target⟩ ∧
      (request snapshot book semantics ambient command).verb = command.verb ∧
      (request snapshot book semantics ambient command).policyId = ⟨command.target⟩ ∧
      (request snapshot book semantics ambient command).subject = command.subject :=
  ⟨rfl, rfl, rfl, rfl⟩

def family (snapshot : Snapshot) (book : BookMaterialized) (semantics : Digest) (ambient : Ambient)
    (command : Command) (plan : Plan) :
    SemanticEffectFamily CanonicalResourceKernel.layout
      (CanonicalCellRegistry.materializer .resourceBook) Nat where
  Declaration := Declaration
  declarationCodec := declarationCodec
  pre := book
  request := fun d => (context snapshot semantics ambient command).request
    declarationCodec (effectDigest snapshot.domain semantics command) book.root
    d.operationNullifier d
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun _ _ => Unit
  Postcondition := fun _ _ post => (plan.batch.patch book).ResultAt book.logical post
  effectDigest := effectDigest snapshot.domain semantics command
  patch := fun _ _ => plan.batch.patch book
  nullifier := fun d _ => some d.operationNullifier
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

def requireSome {A : Type} (reason : Reject) : Option A → Except Reject A
  | none => .error reason
  | some value => .ok value

/-- The Book the observed cell holds. -/
def bookOf {deployment : Deployment} {directory : Directory Nat Registry}
    (book : BookCell deployment directory) : Book :=
  CanonicalResourceKernel.logicalBook book.payload.logical

/-! ## Preparation -/

structure Prepared {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (command : Command) where
  private mk ::
  directory : LoadedDirectory durable
  authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot
  book : BookCell deployment directory.directory
  plan : Plan
  decided : decideWell (bookOf book) authority.snapshot.authState.parent ambient.credit command =
    .ok plan
  candidate : Candidate (family authority.snapshot book.payload profile.semantics ambient command plan)
    book.payload (declaration authority.snapshot.domain profile.semantics command) ()
  source : CanonicalCellRegistry.LoadedPolicySource authority.snapshot.domain directory.directory
    (authority.snapshot.authState.policyAddress ⟨command.target⟩
      (authority.snapshot.authState.policyRevision ⟨command.target⟩))

/-- The decision, in order: the loaded directory, authority and Book; the pure
`decideWell` (which includes the Book admission); the operation marker; the
target law's source. Refusals before the signature check are named. -/
def prepare {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (command : Command) : Except Reject (Prepared deployment profile ambient durable command) := do
  let directory ← requireSome .directoryUnavailable (loadDirectory durable)
  let authority ← requireSome .authorityUnavailable (loadDeployment deployment durable.snapshot)
  let book ← requireSome .bookUnavailable
    (ResourceBirthController.Concrete.observeCell deployment directory.directory
      deployment.resourceBookId .resourceBook)
  let snapshot := authority.snapshot
  match decided : decideWell (bookOf book) snapshot.authState.parent ambient.credit command with
  | .error reason => throw reason
  | .ok plan =>
    let d := declaration snapshot.domain profile.semantics command
    if snapshot.spent d.operationNullifier = false then
      let source ← requireSome .policyUnavailable (CanonicalCellRegistry.loadPolicySource
        snapshot.domain directory.directory
        (snapshot.authState.policyAddress ⟨command.target⟩
          (snapshot.authState.policyRevision ⟨command.target⟩)))
      let candidate : Candidate (family snapshot book.payload profile.semantics ambient command plan)
          book.payload d () :=
        { preStateBound := rfl
          modeEvidence := ()
          validated := plan.batch.validated book.payload
          postcondition := (plan.batch.validated book.payload).resultAt }
      pure ⟨directory, authority, book, plan, decided, candidate, source⟩
    else throw .replayedMarker

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {command : Command}

/-- The Book after the command: the decided batch applied. -/
def Prepared.bookPost (prepared : Prepared deployment profile ambient durable command) :
    BookMaterialized :=
  prepared.candidate.validated.apply

/-- The prepared Book is exactly the decided batch applied to the loaded Book. -/
theorem Prepared.bookPost_exact (prepared : Prepared deployment profile ambient durable command) :
    CanonicalResourceKernel.logicalBook prepared.bookPost.logical =
      prepared.plan.batch.apply (bookOf prepared.book) :=
  CanonicalResourceKernel.logicalBook_run_bookPatch _ _

/-- A prepared command never touches the credit asset. -/
theorem Prepared.credit_untouched (prepared : Prepared deployment profile ambient durable command)
    (holder : AccountId) :
    (CanonicalResourceKernel.logicalBook prepared.bookPost.logical).balance holder ambient.credit =
      (bookOf prepared.book).balance holder ambient.credit := by
  rw [prepared.bookPost_exact]
  exact credit_well_untouched prepared.decided holder

def project (prepared : Prepared deployment profile ambient durable command)
    (logical : Store CanonicalResourceKernel.layout) : Minidregg.Pred.State :=
  ⟨WorldKindLawDependencies.targetSelectorSlots prepared.directory.directory command.target ++
    CanonicalRuntimeProfile.requestSlots
      (request prepared.authority.snapshot prepared.book.payload profile.semantics ambient command) ++
    [("authority/operation/well", 1),
     ("well/asset", Int.ofNat command.well),
     ("well/realm", Int.ofNat prepared.plan.realm),
     ("well/op", match command.op with | .mint => 0 | .burn => 1),
     ("well/account", Int.ofNat command.account),
     ("well/amount", Int.ofNat command.amount),
     ("well/supply", -((CanonicalResourceKernel.logicalBook logical).balance command.well command.well))] ++
    ResourceAuthorityProjection.grantSlots "authority/grant" .account command.capability
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
  WorldKindLawDependencies.loadTarget deployment prepared.directory.directory command.target

def policyConfig [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command) : ComposedPolicyAdmission.Config F :=
  PhysicalLawResolution.config profile.compilerProfile prepared.authority.snapshot
    prepared.directory.directory
    (sourceCapabilityPortal prepared.authority.snapshot
      (marker prepared.authority.snapshot.domain profile.semantics command))
    (step prepared) command.target
    ((kindDependencies prepared).map (·.additional) |>.getD [])

def lawReadGuards (prepared : Prepared deployment profile ambient durable command) :
    Option (List (Nat × Digest)) := do
  let structural ← kindDependencies prepared
  let sources ← PhysicalLawResolution.readGuards prepared.authority.snapshot
    prepared.directory.directory profile.semantics command.target structural.additional
  pure (sources ++ structural.readGuards)

abbrev Prepared.SemanticAccepted [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command) :=
  AcceptedCellEffect (portal := (policyConfig prepared).portal)
    (authState := prepared.authority.snapshot.authState)
    (family prepared.authority.snapshot prepared.book.payload profile.semantics ambient command
      prepared.plan)
    (request prepared.authority.snapshot prepared.book.payload profile.semantics ambient command)
    prepared.book.payload
    (declaration prepared.authority.snapshot.domain profile.semantics command) ()

/-- Capability evidence for the request's target and verb (`noGrant` when the
presented stored capability does not cover it), then the target's law over the
projected request (`lawRefused`). -/
def authorize [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command)
    (receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot) :
    Except Reject prepared.SemanticAccepted := do
  let wanted := request prepared.authority.snapshot prepared.book.payload profile.semantics ambient
    command
  let config := policyConfig prepared
  let _ ← requireSome .policyUnavailable (kindDependencies prepared)
  let evidence ← requireSome .noGrant
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
  | none => .error .lawRefused
  | some authorization =>
      .ok (prepared.candidate.accept authorization rfl rfl rfl .sealed trivial)

/-- The portal of this receiver has no signature-mode and no proof-mode
witness: every admitted command invokes a stored capability. -/
theorem signature_mode_refuted [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command) :
    IsEmpty (policyConfig prepared).portal.SignatureWitness ∧
      IsEmpty (policyConfig prepared).portal.ProofWitness := by
  unfold policyConfig
  exact ⟨⟨fun witness => nomatch witness⟩, ⟨fun witness => nomatch witness⟩⟩

/-- The request this prepared command signs and is authorized as. -/
def Prepared.wanted (prepared : Prepared deployment profile ambient durable command) :
    Request .account :=
  request prepared.authority.snapshot prepared.book.payload profile.semantics ambient command

/-- **Grant and law.** Every accepted well command carries capability-mode
evidence: a capability admissible (holder, window, epochs, scope covering the
target, verb in scope, non-revoked) for the exact request — target, verb and
governing law the command names — AND the target law's committed predicate
verified over that request. -/
theorem well_command_requires_grant_and_law [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command)
    (semantic : prepared.SemanticAccepted) :
    prepared.wanted.target = ⟨command.target⟩ ∧ prepared.wanted.verb = command.verb ∧
      prepared.wanted.policyId = ⟨command.target⟩ ∧
      (∃ cap : Capability .account, ∃ commitment : Digest,
        semantic.authorization.evidence.capabilityValue = some (cap, commitment) ∧
        cap.Admissible prepared.authority.snapshot.authState prepared.wanted) ∧
      (policyConfig prepared).portal.verifyCommittedPolicy
        (prepared.authority.snapshot.authState.policyAddress prepared.wanted.policyId
          prepared.wanted.policyRevision) prepared.wanted
        semantic.authorization.policyWitness = true := by
  obtain ⟨noSignature, noProof⟩ := signature_mode_refuted prepared
  refine ⟨rfl, rfl, rfl, ?_, semantic.authorization.policyVerified⟩
  match semantic.authorization.evidence with
  | .signature witness _ _ => exact (noSignature.false witness).elim
  | .proof witness _ => exact (noProof.false witness).elim
  | .capability cap commitment _ _ _ _ _ admissible _ _ _ _ _ _ _ =>
      exact ⟨cap, commitment, rfl, admissible⟩

/-- **`well_mint_requires_grant_and_law`**: an accepted mint was authorized by a
capability admissible for the request on the WELL itself whose scope holds
`mintAsset`, and the well's own law verified that request. -/
theorem well_mint_requires_grant_and_law [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command)
    (semantic : prepared.SemanticAccepted) (mint : command.op = .mint) :
    prepared.wanted.target = ⟨command.well⟩ ∧ prepared.wanted.verb = .mintAsset ∧
      prepared.wanted.policyId = ⟨command.well⟩ ∧
      (∃ cap : Capability .account, ∃ commitment : Digest,
        semantic.authorization.evidence.capabilityValue = some (cap, commitment) ∧
        cap.Admissible prepared.authority.snapshot.authState prepared.wanted ∧
        Verb.mintAsset ∈ cap.scope.verbs) ∧
      (policyConfig prepared).portal.verifyCommittedPolicy
        (prepared.authority.snapshot.authState.policyAddress ⟨command.well⟩
          prepared.wanted.policyRevision) prepared.wanted
        semantic.authorization.policyWitness = true := by
  obtain ⟨target, verb, policy, ⟨cap, commitment, named, admissible⟩, law⟩ :=
    well_command_requires_grant_and_law prepared semantic
  have targetWell : command.target = command.well := by simp [Command.target, mint]
  have verbMint : command.verb = .mintAsset := by simp [Command.verb, mint]
  rw [targetWell] at target policy
  rw [verbMint] at verb
  have allowed := admissible.scope.verb
  rw [verb] at allowed
  -- `mintAsset` has itself as its only grantor (`Verb.grantors`).
  have inScope : Verb.mintAsset ∈ cap.scope.verbs := by
    obtain ⟨granted, grantor, held⟩ := allowed
    simp only [Verb.grantors, List.mem_singleton] at grantor
    exact grantor ▸ held
  rw [policy] at law
  exact ⟨target, verb, policy, ⟨cap, commitment, named, admissible, inScope⟩, law⟩

/-- Refuting pole of the grant half: when the presented capability yields no
evidence for the request, `authorize` refuses `noGrant` before any law. -/
theorem no_grant_refused [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command)
    (receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot)
    (none : sourceCapabilityOnlyEvidence profile.compilerProfile prepared.authority.snapshot
      (sourceStore prepared)
      (marker prepared.authority.snapshot.domain profile.semantics command) (step prepared)
      (request prepared.authority.snapshot prepared.book.payload profile.semantics ambient command)
      command.capability receipt = none) :
    authorize prepared receipt = .error .noGrant := by
  unfold authorize
  simp only [none, requireSome, bind, Except.bind]

structure Accepted [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command)
    (ingress : Ingress) where
  private mk ::
  receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot
  envelopeExact : receipt.envelopeBytes = ingress.envelope
  semantic : prepared.SemanticAccepted

/-! ## Decoded ingress -/

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

def admitNative [DecidableEq F] (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared deployment profile ambient durable command)
    (ingress : Ingress) : IO (Except Reject (Accepted prepared ingress)) := do
  match ← CredentialSignatureAdmission.verifyNative native prepared.authority.snapshot
      (marker prepared.authority.snapshot.domain profile.semantics command)
      (request prepared.authority.snapshot prepared.book.payload profile.semantics ambient command)
      ingress.envelope with
  | .error reason => return .error (.signature reason)
  | .ok receipt =>
      if same : receipt.envelopeBytes = ingress.envelope then
        match authorize prepared receipt with
        | .error reason => return .error reason
        | .ok semantic => return .ok ⟨receipt, same, semantic⟩
      else return .error .noGrant

/-- The exact header the subject signs over the current image. It discloses no
decision: a refused command still receives a header. -/
def signingHeader (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) :
    Except String CredentialSignedEnvelopeController.SignedHeader := do
  let some authority := loadDeployment deployment durable.snapshot
    | .error "authority unavailable"
  let some directory := loadDirectory durable
    | .error "directory unavailable"
  let some book := ResourceBirthController.Concrete.observeCell deployment directory.directory
      deployment.resourceBookId .resourceBook
    | .error "book unavailable"
  (CredentialSignatureAdmission.signingHeader authority.snapshot
    (marker deployment.domain profile.semantics command)
    ⟨.account, request authority.snapshot book.payload profile.semantics ambient command⟩).mapError
      (fun reason => s!"well signer key: {repr reason}")

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

def bookWrite (prepared : Prepared deployment profile ambient durable command) : DataWrite :=
  ResourceBirthController.Concrete.packedWrite deployment.resourceBookId
    ⟨.resourceBook, prepared.book.payload⟩ ⟨.resourceBook, prepared.bookPost⟩

def writes (prepared : Prepared deployment profile ambient durable command) : List DataWrite :=
  [bookWrite prepared]

def policyGuard (prepared : Prepared deployment profile ambient durable command) : ReadGuard :=
  ⟨⟨prepared.source.readGuard.1⟩, prepared.source.readGuard.2⟩

def readGuards (prepared : Prepared deployment profile ambient durable command) : List ReadGuard :=
  policyGuard prepared ::
    (prepared.authority.readGuards ++
      ((lawReadGuards prepared).getD []).map (fun (id, root) => ⟨⟨id⟩, root⟩)).filter fun guard => guard.cellId ∉ (writes prepared).map DataWrite.cellId

def PhysicalShape (prepared : Prepared deployment profile ambient durable command) : Prop :=
  ((writes prepared).map DataWrite.cellId).Nodup ∧
    (∀ write ∈ writes prepared, write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
    (∀ write ∈ writes prepared, ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
    (∀ write ∈ writes prepared, rootBytes write.canonicalPostBytes = write.exactPost) ∧
    (policyGuard prepared).cellId ∉ (writes prepared).map DataWrite.cellId ∧
    (∀ guard ∈ readGuards prepared, guard.expectedRoot = durable.snapshot.model.roots guard.cellId) ∧
    (lawReadGuards prepared).isSome = true

instance physicalShapeDecidable (prepared : Prepared deployment profile ambient durable command) :
    Decidable (PhysicalShape prepared) := by
  unfold PhysicalShape
  infer_instance

theorem readGuards_readonly (prepared : Prepared deployment profile ambient durable command)
    (shape : PhysicalShape prepared) (guard : ReadGuard) (member : guard ∈ readGuards prepared) :
    guard.cellId ∉ (writes prepared).map DataWrite.cellId := by
  rcases List.mem_cons.mp member with rfl | authority
  · exact shape.2.2.2.2.1
  · simpa using (List.mem_filter.mp authority).2

structure AcceptedWell [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (ingress : DecodedIngress) where
  private mk ::
  prepared : Prepared deployment profile ambient durable ingress.command
  accepted : RealmWellReceiver.Accepted prepared ingress.ingress
  physical : PhysicalShape prepared

def admitDecodedNative [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (native : CredentialSignatureIO.NativeConfig) (ingress : DecodedIngress) :
    IO (Except Reject (AcceptedWell deployment profile ambient durable ingress)) := do
  match prepare deployment profile ambient durable ingress.command with
  | .error reason => return .error reason
  | .ok prepared =>
    if physical : PhysicalShape prepared then
      match ← admitNative native prepared ingress.ingress with
      | .error reason => return .error reason
      | .ok accepted => return .ok ⟨prepared, accepted, physical⟩
    else return .error .physicalPreparation

variable [DecidableEq F] {ingress : DecodedIngress}

/-- The accepted well command's grant-and-law fact, at the receiver. -/
theorem AcceptedWell.grant_and_law (accepted : AcceptedWell deployment profile ambient durable ingress)
    (mint : ingress.command.op = .mint) :
    accepted.prepared.wanted.target = ⟨ingress.command.well⟩ ∧
      accepted.prepared.wanted.verb = .mintAsset ∧
      (∃ cap : Capability .account, ∃ commitment : Digest,
        accepted.accepted.semantic.authorization.evidence.capabilityValue = some (cap, commitment) ∧
        cap.Admissible accepted.prepared.authority.snapshot.authState accepted.prepared.wanted ∧
        Verb.mintAsset ∈ cap.scope.verbs) := by
  obtain ⟨target, verb, -, grant, -⟩ :=
    well_mint_requires_grant_and_law accepted.prepared accepted.accepted.semantic mint
  exact ⟨target, verb, grant⟩

/-- The accepted Book post is the decided plan applied, and credit is untouched. -/
theorem AcceptedWell.book_exact (accepted : AcceptedWell deployment profile ambient durable ingress) :
    CanonicalResourceKernel.logicalBook accepted.prepared.bookPost.logical =
      accepted.prepared.plan.batch.apply (bookOf accepted.prepared.book) :=
  accepted.prepared.bookPost_exact

def charge (accepted : AcceptedWell deployment profile ambient durable ingress) :
    ResourceCost.Charge
  | .incidences => 1
  | .turnBytes => ingress.bytes.length
  | .memoryTouches => (writes accepted.prepared).length + (readGuards accepted.prepared).length
  | .storageBytes => ((writes accepted.prepared).map fun write => write.canonicalPostBytes.length).sum
  | .witnessBytes => ingress.ingress.envelope.length
  | .proofWork => 2
  | .feeDebit | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

def intent (accepted : AcceptedWell deployment profile ambient durable ingress) :
    DataIntent rootBytes where
  transactionId := transactionId deployment.domain profile.semantics ingress
  subject := some ingress.command.subject
  writes := writes accepted.prepared
  readGuards := readGuards accepted.prepared
  nullifiers := [nullifier deployment.domain profile.semantics ingress]
  exactCharge := charge accepted
  event := event deployment.domain profile.semantics ingress
  postRootsBound := fun write member => accepted.physical.2.2.2.1 write member
  guardsReadOnly := readGuards_readonly accepted.prepared accepted.physical

/-- An accepted well command writes exactly the Book. -/
theorem intent_writes_book (accepted : AcceptedWell deployment profile ambient durable ingress) :
    (intent accepted).writes.map DataWrite.cellId = [⟨deployment.resourceBookId⟩] := rfl

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

/-- info: 'Minidregg.Kernel.RealmWellReceiver.decideWell_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decideWell_ok
/-- info: 'Minidregg.Kernel.RealmWellReceiver.credit_well_untouched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms credit_well_untouched
/-- info: 'Minidregg.Kernel.RealmWellReceiver.well_burn_requires_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms well_burn_requires_balance
/-- info: 'Minidregg.Kernel.RealmWellReceiver.decided_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decided_apply
/-- info: 'Minidregg.Kernel.RealmWellReceiver.well_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms well_step
/-- info: 'Minidregg.Kernel.RealmWellReceiver.well_tracks_mints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms well_tracks_mints
/-- info: 'Minidregg.Kernel.RealmWellReceiver.realm_conservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms realm_conservation
/-- info: 'Minidregg.Kernel.RealmWellReceiver.accounts_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accounts_stable
/-- info: 'Minidregg.Kernel.RealmWellReceiver.realm_holders_eq_neg_well' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms realm_holders_eq_neg_well
/-- info: 'Minidregg.Kernel.RealmWellReceiver.AcceptedLog.snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AcceptedLog.snoc
/-- info: 'Minidregg.Kernel.RealmWellReceiver.decided_extends_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decided_extends_log
/-- info: 'Minidregg.Kernel.RealmWellReceiver.pole_mint_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pole_mint_admitted
/-- info: 'Minidregg.Kernel.RealmWellReceiver.pole_mint_then_burn_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pole_mint_then_burn_admitted
/-- info: 'Minidregg.Kernel.RealmWellReceiver.pole_overburn_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pole_overburn_refused
/-- info: 'Minidregg.Kernel.RealmWellReceiver.pole_credit_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pole_credit_refused
/-- info: 'Minidregg.Kernel.RealmWellReceiver.pole_rootless_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pole_rootless_refused
/-- info: 'Minidregg.Kernel.RealmWellReceiver.pole_self_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pole_self_refused
/-- info: 'Minidregg.Kernel.RealmWellReceiver.pole_zero_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pole_zero_refused
/-- info: 'Minidregg.Kernel.RealmWellReceiver.pole_unregistered_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pole_unregistered_refused
/-- info: 'Minidregg.Kernel.RealmWellReceiver.pole_log_tracks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pole_log_tracks
/-- info: 'Minidregg.Kernel.RealmWellReceiver.request_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms request_target
/-- info: 'Minidregg.Kernel.RealmWellReceiver.Prepared.bookPost_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Prepared.bookPost_exact
/-- info: 'Minidregg.Kernel.RealmWellReceiver.Prepared.credit_untouched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Prepared.credit_untouched
/-- info: 'Minidregg.Kernel.RealmWellReceiver.signature_mode_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms signature_mode_refuted
/-- info: 'Minidregg.Kernel.RealmWellReceiver.well_command_requires_grant_and_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms well_command_requires_grant_and_law
/-- info: 'Minidregg.Kernel.RealmWellReceiver.well_mint_requires_grant_and_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms well_mint_requires_grant_and_law
/-- info: 'Minidregg.Kernel.RealmWellReceiver.no_grant_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_grant_refused
/-- info: 'Minidregg.Kernel.RealmWellReceiver.readGuards_readonly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readGuards_readonly
/-- info: 'Minidregg.Kernel.RealmWellReceiver.AcceptedWell.grant_and_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AcceptedWell.grant_and_law
/-- info: 'Minidregg.Kernel.RealmWellReceiver.AcceptedWell.book_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AcceptedWell.book_exact
/-- info: 'Minidregg.Kernel.RealmWellReceiver.intent_writes_book' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms intent_writes_book

end Minidregg.Kernel.RealmWellReceiver
