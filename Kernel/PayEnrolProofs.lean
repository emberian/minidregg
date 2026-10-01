/-
# Kernel.PayEnrolProofs — what an accepted self-enrollment turn does (PAY §11.4, P3b-2)

* `multi_cell_intent_atomic` — the step-0 answer as a theorem: ONE `DataIntent`
  writing any number of distinct cells installs every write or none, whatever
  the crash schedule.  No intent-layer extension was needed; resource birth
  already writes allocations, the factory, the Book and the authority cell in
  one intent.
* `enrol_atomic` — an accepted enrollment writes the authority cell, the
  factory, the Book and the pay cell in that one intent, all or none.
* `self_enroll_nullifier` — the transfer's `soltx:‖sig‖addr` nullifier, once
  consumed, refuses any later enrollment turn for it (P3's
  `second_credit_refused`, here for the enrollment receiver).
* `enrolled_key_has_no_grant_beyond_membership` — the enrollment changes the
  authority cell's capability planes at exactly three addresses: the new
  subject's owner and control grants on its own account and its
  factory-observation grant.
* `journal_mints_nothing` — a journaled payment writes the pay cell only.
* `renew_only_extends` — a renewal writes the pay cell and the Book; the pay
  patch is the clock and the enrolment row's lease, which never shortens.
* `observer_control_confined` is `NativeHostGenesis.observer_control_confined`.
-/
import Kernel.PayEnrolReceiver

namespace Minidregg.Kernel.PayEnrolProofs

open Minidregg.Compiler
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.PayCell
open Minidregg.Kernel.PayTariff
open Minidregg.Kernel.PayEnrolMemo
open Minidregg.Kernel.PayEnrolDecision
open Minidregg.Kernel.PayEnrolReceiver
open Minidregg.Kernel.PayObservation (Observation nullifier tickNullifier)
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialAuthorityEffects
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.Store (Store Patch Address)
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## Step 0: one intent, many cells, all or nothing -/

theorem lookupPostBytes_member :
    ∀ {writes : List DataWrite}, (writes.map DataWrite.cellId).Nodup →
      ∀ {write : DataWrite}, write ∈ writes →
        DataSnapshot.lookupPostBytes write.cellId writes = some write.canonicalPostBytes
  | [], _, _, member => by cases member
  | first :: rest, distinct, write, member => by
      simp only [List.map_cons, List.nodup_cons] at distinct
      rcases List.mem_cons.mp member with rfl | later
      · simp [DataSnapshot.lookupPostBytes]
      · have other : first.cellId ≠ write.cellId := fun same =>
          distinct.1 (same ▸ List.mem_map_of_mem later)
        simp only [DataSnapshot.lookupPostBytes, other, if_false]
        exact lookupPostBytes_member distinct.2 later

/-- **`multi_cell_intent_atomic`**: whatever the crash schedule, after
`execute` either no write of the intent is visible or every one is, each cell
holding exactly its declared post bytes. -/
theorem multi_cell_intent_atomic {rootBytes : List UInt8 → Digest} (schedule : Schedule)
    (before : DataSnapshot rootBytes) (intent : DataIntent rootBytes)
    (distinct : (intent.writes.map DataWrite.cellId).Nodup) :
    (∀ write ∈ intent.writes,
        ((execute schedule before intent).storeAfter before).canonicalBytes write.cellId =
          before.canonicalBytes write.cellId) ∨
      (∀ write ∈ intent.writes,
        ((execute schedule before intent).storeAfter before).canonicalBytes write.cellId =
          write.canonicalPostBytes) := by
  rcases execute_no_partial_data_commit schedule before intent with same | installed
  · left
    intro write _
    rw [same]
  · right
    intro write member
    rw [installed, DataSnapshot.install_canonicalBytes, lookupPostBytes_member distinct member]
    rfl

/-! ## The legs, per decision -/

section Legs

variable {F : Type} [Field F] {deployment : CanonicalCellRegistry.Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {directory : LoadedDirectory durable} {authority : Loaded deployment durable.snapshot}
  {pay : PayCellDomain.Loaded deployment durable.snapshot}
  {book : PayEnrolReceiver.BookCell deployment directory.directory} {tariff : Tariff} {price : Price}

theorem legs_enrol_cells (factory : FactoryCell deployment directory.directory) (plan : EnrolPlan) :
    ∀ {decision : Decision}
      (legs : Legs deployment profile ambient directory authority pay book tariff price decision),
      decision = .enrol plan →
        cellIdOf deployment ∈ (legs.writes factory).map DataWrite.cellId ∧
        (⟨deployment.factoryId⟩ : CellId) ∈ (legs.writes factory).map DataWrite.cellId ∧
        (⟨deployment.resourceBookId⟩ : CellId) ∈ (legs.writes factory).map DataWrite.cellId
  | _, .enrol _ _, _ => by
      simp [Legs.writes, ResourceBirthController.Concrete.planWrites, Loaded.writes, Loaded.write,
        ResourceBirthController.Concrete.packedWrite]
  | _, .renew _ _ _ _, same => by cases same
  | _, .journal _, same => by cases same

theorem legs_journal_writes (factory : FactoryCell deployment directory.directory)
    (reason : JournalReason) :
    ∀ {decision : Decision}
      (legs : Legs deployment profile ambient directory authority pay book tariff price decision),
      decision = .journal reason → legs.writes factory = []
  | _, .journal _, _ => rfl
  | _, .enrol _ _, same => by cases same
  | _, .renew _ _ _ _, same => by cases same

theorem legs_journal_patch (command : Command) (reason : JournalReason) :
    ∀ {decision : Decision}
      (legs : Legs deployment profile ambient directory authority pay book tariff price decision),
      decision = .journal reason →
        patchOf command legs = journalPatch command.observation reason
  | _, .journal _, same => by cases same; rfl
  | _, .enrol _ _, same => by cases same
  | _, .renew _ _ _ _, same => by cases same

theorem legs_renew_writes (factory : FactoryCell deployment directory.directory) (plan : RenewPlan) :
    ∀ {decision : Decision}
      (legs : Legs deployment profile ambient directory authority pay book tariff price decision),
      decision = .renew plan →
        (legs.writes factory).map DataWrite.cellId = [⟨deployment.resourceBookId⟩]
  | _, .renew _ _ _ _, _ => rfl
  | _, .enrol _ _, same => by cases same
  | _, .journal _, same => by cases same

theorem legs_renew_patch (command : Command) (plan : RenewPlan) :
    ∀ {decision : Decision}
      (legs : Legs deployment profile ambient directory authority pay book tariff price decision),
      decision = .renew plan →
        ∃ record, enrolmentAt pay.cell.logical plan.memo.miniKey = some record ∧
          patchOf command legs =
            [.write .enrolment plan.memo.miniKey record { record with leaseUntil := plan.leaseUntil }]
  | _, .renew _ record recordExact _, same => by
      cases same
      exact ⟨record, recordExact, rfl⟩
  | _, .enrol _ _, same => by cases same
  | _, .journal _, same => by cases same

end Legs

/-! ## The enrollment's authority delta -/

section Authority

variable {F : Type} [Field F] {deployment : CanonicalCellRegistry.Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {directory : LoadedDirectory durable} {authority : Loaded deployment durable.snapshot}
  {book : PayEnrolReceiver.BookCell deployment directory.directory} {tariff : Tariff} {price : Price}
  {plan : EnrolPlan}

/-- The birth part of an enrollment is the template birth: one account law,
an owner grant and a control grant, both held by the new subject. -/
theorem enrol_descriptor_exact
    (legs : EnrolLegs deployment profile ambient directory authority book tariff price plan) :
    legs.descriptor.grants =
        [ownerGrant profile.template authority.snapshot.cell ambient.height (enrolIds deployment plan),
          controlGrant profile.template authority.snapshot.cell ambient.height
            (enrolIds deployment plan)] ∧
      legs.descriptor.initialPolicies =
        [initialPolicy deployment profile.semantics (enrolIds deployment plan)] := by
  have grants := congrArg Descriptor.grants legs.descriptorExact
  have policies := congrArg Descriptor.initialPolicies legs.descriptorExact
  exact ⟨by simpa [enrolDraft, draft] using grants, by simpa [enrolDraft, draft] using policies⟩

/-- The authority cell after an enrollment is the loaded cell with exactly the
enrollment's entries set. -/
theorem enrol_authority_post
    (legs : EnrolLegs deployment profile ambient directory authority book tariff price plan) :
    legs.authorityPost.logical =
      setAll authority.snapshot.logical
        (authorityEntries legs.descriptor (enrolKey deployment authority plan)
          (enrolObserve deployment profile ambient authority plan)) := by
  unfold EnrolLegs.authorityPost
  rw [ValidatedPatch.apply_logical]
  exact run_assignAll _ _

/-- The three grants the enrollment issues, by their authority address. -/
def enrolGrantFields (deployment : CanonicalCellRegistry.Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient)
    (authority : Loaded deployment durable.snapshot) (plan : EnrolPlan) :
    List (Address CredentialAuthorityState.layout) :=
  [ResourceBirthAuthority.grantField
      (ownerGrant profile.template authority.snapshot.cell ambient.height (enrolIds deployment plan)),
    ResourceBirthAuthority.grantField
      (controlGrant profile.template authority.snapshot.cell ambient.height (enrolIds deployment plan)),
    ResourceBirthAuthority.grantField (enrolObserve deployment profile ambient authority plan)]

def isCapabilityAddress : Address CredentialAuthorityState.layout → Bool
  | ⟨.capability _, _⟩ => true
  | _ => false

/-- The capability-plane addresses an enrollment sets are exactly its three
grants; its other entries are the account law's policy rows and the key. -/
theorem enrol_capability_addresses
    (legs : EnrolLegs deployment profile ambient directory authority book tariff price plan) :
    ((authorityEntries legs.descriptor (enrolKey deployment authority plan)
        (enrolObserve deployment profile ambient authority plan)).map Sigma.fst).filter
          isCapabilityAddress =
      enrolGrantFields deployment profile ambient authority plan := by
  have exact := enrol_descriptor_exact legs
  -- An enrollment's account is born at the root (no room), so it records no parent row.
  have rows : legs.descriptor.parentRows = [] := by
    have births := congrArg Descriptor.births legs.descriptorExact
    simp only [Descriptor.parentRows]
    rw [births]
    simp [enrolDraft, draft, birthItem]
  simp only [authorityEntries, ResourceBirthAuthority.entries, exact.1, exact.2, rows]
  rfl

/-- **`enrolled_key_has_no_grant_beyond_membership`**: an enrollment changes
the authority cell's capability planes at exactly the new subject's three
grants, and installs each of them: the owner grant (`ownerVerbs .account`) and
the control grant (`installPolicy`, `revokeCapability`) on its OWN new
account, and `observeObject` on the factory (`enrol_grants_scoped`).  No other
capability anywhere changes, so the new key gains no authority over any other
friend's cell. -/
theorem enrolled_key_has_no_grant_beyond_membership
    (legs : EnrolLegs deployment profile ambient directory authority book tariff price plan) :
    (∀ (kind : ResourceKind) (id : CapabilityId),
      legs.authorityPost.logical ⟨.capability kind, id⟩ ≠
          authority.snapshot.logical ⟨.capability kind, id⟩ →
        (⟨.capability kind, id⟩ : Address CredentialAuthorityState.layout) ∈
          enrolGrantFields deployment profile ambient authority plan) ∧
    (∀ grant ∈ [ownerGrant profile.template authority.snapshot.cell ambient.height
          (enrolIds deployment plan),
        controlGrant profile.template authority.snapshot.cell ambient.height (enrolIds deployment plan),
        enrolObserve deployment profile ambient authority plan],
      legs.authorityPost.logical (ResourceBirthAuthority.grantField grant) = some grant.capability) := by
  have exact := enrol_descriptor_exact legs
  have post := enrol_authority_post legs
  refine ⟨?_, ?_⟩
  · intro kind id changed
    by_contra outside
    apply changed
    rw [post]
    apply setAll_frame
    intro member
    apply outside
    rw [← enrol_capability_addresses legs]
    exact List.mem_filter.mpr ⟨member, rfl⟩
  · intro grant member
    rw [post]
    exact setAll_member authority.snapshot.logical
      (authorityEntries legs.descriptor (enrolKey deployment authority plan)
        (enrolObserve deployment profile ambient authority plan)) legs.entriesDistinct
      (ResourceBirthAuthority.grantEntry grant) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;>
          simp [authorityEntries, ResourceBirthAuthority.entries, exact.1])

/-- The three grants' holders, targets and verbs, by construction. -/
theorem enrol_grants_scoped (template : CanonicalRuntimeProfile.FactoryTemplate)
    (cell : CredentialAuthorityDomain.Cell) (height : Height) (identities : Ids)
    (deployment : CanonicalCellRegistry.Deployment) :
    (ownerGrant template cell height identities).capability.head.holder = .subject ⟨identities.subject⟩ ∧
    (ownerGrant template cell height identities).capability.head.scope.targets =
      .explicit {⟨identities.account⟩} ∧
    (controlGrant template cell height identities).capability.head.holder =
      .subject ⟨identities.subject⟩ ∧
    (controlGrant template cell height identities).capability.head.scope.targets =
      .explicit {⟨identities.account⟩} ∧
    (observeGrant deployment template cell height identities).capability.head.holder =
      .subject ⟨identities.subject⟩ ∧
    (observeGrant deployment template cell height identities).capability.head.scope.targets =
      .explicit {⟨deployment.factoryId⟩} :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Authority

/-! ## The accepted turn -/

section Accepted

variable {F : Type} [Field F] [DecidableEq F] {deployment : CanonicalCellRegistry.Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {ingress : DecodedIngress}

theorem intent_writes_pay (accepted : AcceptedEnrol deployment profile ambient durable ingress) :
    ((intent accepted).writes.map DataWrite.cellId).head? = some (PayCellDomain.cellIdOf deployment) :=
  rfl

/-- **`enrol_atomic`**: an accepted enrollment writes the authority cell, the
factory, the Book and the pay cell in its one intent, and every outcome of
`execute` exposes all of its writes or none. -/
theorem enrol_atomic (accepted : AcceptedEnrol deployment profile ambient durable ingress)
    (plan : EnrolPlan) (enrolled : accepted.prepared.decision = .enrol plan)
    (schedule : Schedule) (before : DataSnapshot rootBytes) :
    (cellIdOf deployment ∈ (intent accepted).writes.map DataWrite.cellId ∧
      (⟨deployment.factoryId⟩ : CellId) ∈ (intent accepted).writes.map DataWrite.cellId ∧
      (⟨deployment.resourceBookId⟩ : CellId) ∈ (intent accepted).writes.map DataWrite.cellId ∧
      PayCellDomain.cellIdOf deployment ∈ (intent accepted).writes.map DataWrite.cellId) ∧
    ((∀ write ∈ (intent accepted).writes,
        ((execute schedule before (intent accepted)).storeAfter before).canonicalBytes write.cellId =
          before.canonicalBytes write.cellId) ∨
      (∀ write ∈ (intent accepted).writes,
        ((execute schedule before (intent accepted)).storeAfter before).canonicalBytes write.cellId =
          write.canonicalPostBytes)) := by
  obtain ⟨authorityCell, factoryCell, bookCell⟩ :=
    legs_enrol_cells accepted.prepared.factory plan accepted.prepared.legs enrolled
  refine ⟨⟨?_, ?_, ?_, ?_⟩, multi_cell_intent_atomic schedule before (intent accepted)
    accepted.physical.1⟩
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ authorityCell)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ factoryCell)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ bookCell)
  · exact List.mem_cons_self

/-- **`self_enroll_nullifier`**: every accepted turn of this receiver spends
the transfer's nullifier, so a durable snapshot that has consumed it refuses
the turn at preflight (`DataIntent.consumed_nullifier_refused`). -/
theorem self_enroll_nullifier (accepted : AcceptedEnrol deployment profile ambient durable ingress)
    (before : DataSnapshot rootBytes)
    (spent : before.model.consumed (nullifier deployment.domain ingress.command.observation) = true) :
    (intent accepted).preflight before ≠ .ok () :=
  DataIntent.consumed_nullifier_refused before (intent accepted) _ List.mem_cons_self spent

/-- The tip's tick nullifier is spent too: one report per tip slot, across
both pay receivers. -/
theorem self_enroll_tick (accepted : AcceptedEnrol deployment profile ambient durable ingress)
    (before : DataSnapshot rootBytes)
    (spent : before.model.consumed (tickNullifier deployment.domain ingress.command.tip) = true) :
    (intent accepted).preflight before ≠ .ok () :=
  DataIntent.consumed_nullifier_refused before (intent accepted) _
    (List.mem_cons_of_mem _ List.mem_cons_self) spent

/-- **`journal_mints_nothing`**: a journaled payment writes the pay cell and the
clock cell and nothing else — no Book write, so no mint — and its pay patch is
exactly the journal row. -/
theorem journal_mints_nothing (accepted : AcceptedEnrol deployment profile ambient durable ingress)
    (reason : JournalReason) (journaled : accepted.prepared.decision = .journal reason) :
    (intent accepted).writes.map DataWrite.cellId =
        [PayCellDomain.cellIdOf deployment, ClockCellDomain.cellIdOf deployment] ∧
    patchOf ingress.command accepted.prepared.legs = journalPatch ingress.command.observation reason ∧
    ∀ (before : DataSnapshot rootBytes) (cellId : CellId), cellId ≠ PayCellDomain.cellIdOf deployment →
      cellId ≠ ClockCellDomain.cellIdOf deployment →
      (DataSnapshot.install before (intent accepted)).canonicalBytes cellId =
        before.canonicalBytes cellId := by
  have empty := legs_journal_writes accepted.prepared.factory reason accepted.prepared.legs journaled
  refine ⟨?_, legs_journal_patch _ reason accepted.prepared.legs journaled, ?_⟩
  · change (payWrite accepted.prepared :: clockWrite accepted.prepared ::
      accepted.prepared.legs.writes accepted.prepared.factory).map DataWrite.cellId = _
    rw [empty]
    rfl
  · intro before cellId other otherClock
    rw [DataSnapshot.install_canonicalBytes]
    change (DataSnapshot.lookupPostBytes cellId
      (payWrite accepted.prepared :: clockWrite accepted.prepared ::
        accepted.prepared.legs.writes accepted.prepared.factory)).getD _ = _
    rw [empty]
    have pay : (payWrite accepted.prepared).cellId ≠ cellId := fun same => other same.symm
    have clock : (clockWrite accepted.prepared).cellId ≠ cellId := fun same => otherClock same.symm
    simp [DataSnapshot.lookupPostBytes, pay, clock]

/-- **`renew_only_extends`**: a renewal writes the pay cell, the clock cell and
the Book and nothing else; its pay patch is the enrolment row with only its
lease changed, and that lease never shortens and is never behind the tip. -/
theorem renew_only_extends (accepted : AcceptedEnrol deployment profile ambient durable ingress)
    (plan : RenewPlan) (renewed : accepted.prepared.decision = .renew plan) :
    (intent accepted).writes.map DataWrite.cellId =
        [PayCellDomain.cellIdOf deployment, ClockCellDomain.cellIdOf deployment,
          ⟨deployment.resourceBookId⟩] ∧
    ∃ record, enrolmentAt accepted.prepared.pay.cell.logical plan.memo.miniKey = some record ∧
      patchOf ingress.command accepted.prepared.legs =
        [.write .enrolment plan.memo.miniKey record { record with leaseUntil := plan.leaseUntil }] ∧
      record.leaseUntil ≤ plan.leaseUntil ∧ ingress.command.tip.hour ≤ plan.leaseUntil := by
  have bookOnly := legs_renew_writes accepted.prepared.factory plan accepted.prepared.legs renewed
  obtain ⟨record, recorded, patched⟩ :=
    legs_renew_patch ingress.command plan accepted.prepared.legs renewed
  have decided := accepted.prepared.decided
  rw [renewed] at decided
  obtain ⟨record', recorded', -, -, longer, behind, -⟩ := renew_extends_lease_never_shortens decided
  rw [recorded] at recorded'
  cases recorded'
  refine ⟨?_, record, recorded, patched, longer, behind⟩
  change (payWrite accepted.prepared :: clockWrite accepted.prepared ::
    accepted.prepared.legs.writes accepted.prepared.factory).map DataWrite.cellId = _
  rw [List.map_cons, List.map_cons, bookOnly]
  rfl

end Accepted

/-! ## The float nets zero -/

open Minidregg.Theory.CanonicalResourceKernel in
/-- Every operation moves its one posting: the source's balance in the
posting's asset falls by the amount and the destination's rises by it. -/
theorem apply_balance (operation : Operation) (book : Book) (account : AccountId)
    (asset : AssetId) :
    (operation.apply book).balance account asset =
      book.balance account asset
        - (if operation.posting.source = account ∧ operation.posting.asset = asset then
            Int.ofNat operation.posting.amount else 0)
        + (if operation.posting.destination = account ∧ operation.posting.asset = asset then
            Int.ofNat operation.posting.amount else 0) := by
  have spine : (operation.apply book).balance account asset =
      (book.applyPosting operation.posting).balance account asset := by
    cases operation <;> rfl
  rw [spine]
  simp only [Book.applyPosting, Book.balance, DFinsupp.add_apply, DFinsupp.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all <;> omega

open Minidregg.Theory.CanonicalResourceKernel in
theorem registerAccounts_balance :
    ∀ (book : Book) (accounts : List AccountId) (account : AccountId) (asset : AssetId),
      (registerAccounts book accounts).balance account asset = book.balance account asset
  | _, [], _, _ => rfl
  | book, first :: rest, account, asset => by
      rw [registerAccounts, registerAccounts_balance]
      rfl

/-- The birth fee of an enrollment's descriptor does not depend on who pays it
or on the funding: it is the price's birth fee. -/
theorem enrol_descriptor_fee {F : Type} [Field F] {deployment : CanonicalCellRegistry.Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
    {directory : LoadedDirectory durable} {authority : Loaded deployment durable.snapshot}
    {book : PayEnrolReceiver.BookCell deployment directory.directory} {tariff : Tariff}
    {price : Price} {plan : EnrolPlan}
    (legs : EnrolLegs deployment profile ambient directory authority book tariff price plan) :
    legs.descriptor.fee = ⟨plan.float, ambient.tariff.collector, ambient.tariff.asset,
      birthFee deployment profile.semantics profile.template ambient.tariff authority.snapshot.cell
        ambient.height (enrolIds deployment plan) 0⟩ ∧
    legs.descriptor.funding = [⟨plan.float, (enrolIds deployment plan).account, ambient.tariff.asset,
      enrolRemainder tariff price plan⟩] := by
  have fee := congrArg Descriptor.fee legs.descriptorExact
  have funding := congrArg Descriptor.funding legs.descriptorExact
  exact ⟨by simpa [enrolDraft, draft, birthFee] using fee, by simpa [enrolDraft, draft] using funding⟩

/-- **`enrol_float_net_zero`**: the enrollment's Book batch leaves the float
where it started — it mints the credit to the float and pays out exactly the
lease, the remainder and the birth fee — whenever the price is the
descriptor's fee, the credit covers fee and lease, the tariff and factory
share one asset, and the float is neither the issuer well, the new account
nor the collector. -/
theorem enrol_float_net_zero {F : Type} [Field F] {deployment : CanonicalCellRegistry.Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
    {directory : LoadedDirectory durable} {authority : Loaded deployment durable.snapshot}
    {book : PayEnrolReceiver.BookCell deployment directory.directory} {tariff : Tariff}
    {price : Price} {plan : EnrolPlan}
    (legs : EnrolLegs deployment profile ambient directory authority book tariff price plan)
    (fee : legs.descriptor.fee.amount = price.birthFee)
    (afford : price.birthFee + leaseCost tariff plan.weeks ≤ plan.credit)
    (sameAsset : ambient.tariff.asset = tariff.asset)
    (notWell : plan.float ≠ tariff.asset)
    (notAccount : plan.float ≠ (enrolIds deployment plan).account)
    (notCollector : plan.float ≠ ambient.tariff.collector)
    (pre : CanonicalResourceKernel.Book) :
    ((enrolBatch tariff ambient.tariff.collector plan legs.descriptor).apply pre).balance
        plan.float tariff.asset = pre.balance plan.float tariff.asset := by
  obtain ⟨feeExact, fundingExact⟩ := enrol_descriptor_fee legs
  have paid : birthFee deployment profile.semantics profile.template ambient.tariff
      authority.snapshot.cell ambient.height (enrolIds deployment plan) 0 = price.birthFee := by
    rw [feeExact] at fee
    exact fee
  simp only [enrolBatch, CanonicalResourceKernel.Batch.apply, Descriptor.resourceBatch,
    fundingExact, feeExact, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    CanonicalResourceKernel.applyOperations, InitialFunding.operation, CreationFee.operation]
  rw [apply_balance, apply_balance, apply_balance, apply_balance, registerAccounts_balance]
  simp only [CanonicalResourceKernel.Operation.posting, sameAsset, Ne.symm notWell,
    Ne.symm notAccount, Ne.symm notCollector, and_true, if_true, if_false]
  unfold enrolRemainder
  simp only [Int.ofNat_eq_coe]
  omega

/-- An accepted enrollment always covers its birth fee and every lease week it
grants, so the remainder is exact (`enrol_float_net_zero`'s `afford`). -/
theorem enrol_affordable {store : PayStore} {price : Price} {tip : ChainTip} {o : Observation}
    {verified : Verified} {subjectTaken : Bool} {plan : EnrolPlan}
    (accepted : decideEnrol store price tip o verified subjectTaken = .ok (.enrol plan)) :
    ∃ tariff, tariffOf store = some tariff ∧
      price.birthFee + leaseCost tariff plan.weeks ≤ plan.credit := by
  obtain ⟨tariff, credit, present, -, -, -, -, decided⟩ := decideEnrol_ok accepted
  obtain ⟨-, -, -, -, -, -, -, -, priced, planned⟩ := classify_enrol decided.symm
  refine ⟨tariff, present, ?_⟩
  have weeks := congrArg EnrolPlan.weeks planned
  have credited := congrArg EnrolPlan.credit planned
  simp only [enrolPlan] at weeks credited
  have floor := Nat.div_mul_le_self (credit.credit - price.birthFee) tariff.weekCredit
  simp only [enrolPrice] at priced
  unfold leaseCost
  rw [weeks, credited]
  omega

/-! ## Poles -/

/-- Satisfiable pole: the journaled branch's pay patch on a concrete
observation is exactly one journal allocation. -/
theorem journal_patch_length (o : Observation) (reason : JournalReason) :
    (payPatch o (.journal reason) 0 none).length = 1 := rfl

/-- Refuting pole: an enrollment's pay patch is not the journal's — it
allocates the enrolment row, the ssh index and (with a free index) the
assignment. -/
theorem enrol_patch_length (o : Observation) (plan : EnrolPlan)
    (account index : Nat) (free : plan.index = some index) :
    (payPatch o (.enrol plan) account none).length = 3 := by
  simp [payPatch, EnrolPlan.patch, free]

/-- Every lease week granted is paid: at the journeys' rate (5 952 380 credit
per hour) one week costs exactly `168 · rate`. -/
theorem lease_week_cost : leaseCost { exampleTariff with nodeHourRate := 5952380 } 1 = 999999840 := by
  decide +kernel

#assert_axioms lookupPostBytes_member
#assert_axioms multi_cell_intent_atomic
#assert_axioms legs_enrol_cells
#assert_axioms legs_journal_writes
#assert_axioms legs_journal_patch
#assert_axioms legs_renew_writes
#assert_axioms legs_renew_patch
#assert_axioms enrol_descriptor_exact
#assert_axioms enrol_authority_post
#assert_axioms enrol_capability_addresses
#assert_axioms enrolled_key_has_no_grant_beyond_membership
#assert_axioms enrol_grants_scoped
#assert_axioms intent_writes_pay
#assert_axioms enrol_atomic
#assert_axioms self_enroll_nullifier
#assert_axioms self_enroll_tick
#assert_axioms journal_mints_nothing
#assert_axioms renew_only_extends
#assert_axioms apply_balance
#assert_axioms registerAccounts_balance
#assert_axioms enrol_descriptor_fee
#assert_axioms enrol_float_net_zero
#assert_axioms enrol_affordable
#assert_axioms journal_patch_length
#assert_axioms enrol_patch_length
#assert_axioms lease_week_cost

end Minidregg.Kernel.PayEnrolProofs
