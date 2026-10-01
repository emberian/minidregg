/-
# Kernel.PayEnrolDecision — what an enrollment-index payment decides (PAY §11.3–§11.4)

One finalized transfer to the enrollment index (`Tariff.enrolIndex`) is
decided here, purely, over the pay cell:

* **Refused** (`Reject`, nothing consumed): self-enrollment off, not the
  enrollment index, below `journalFloor`, or any of P3's per-observation
  refusals (`PayObservation.decideObservation`, reused, not copied).
* **Journaled** (`Decision.journal reason`, the nullifier is spent, nothing is
  credited): no memo, two memos, a non-UTF-8 memo, a malformed memo (by
  `PayEnrolMemo.Refusal`), a bad Mini signature, a bad ssh signature, the ssh
  key enrolled under another Mini key, the Mini key enrolled with another ssh
  key, a derived subject already taken, or a payment below the price.
* **Renewal** (`Decision.renew`): the Mini key is enrolled with this ssh key;
  the credit goes to its account and the lease grows from
  `max(now, leaseUntil)` by whole node weeks.
* **Enrollment** (`Decision.enrol`): a fresh Mini key and a fresh ssh key,
  both possessions verified, and at least `enrolPrice = birthFee + 168 · rate`
  of credit; the lease runs `⌊(credit − birthFee) / (168 · rate)⌋ ≥ 1` weeks
  from now.

The two signature bits (`Verified`) come from the native verifier through
`Compiler.PayEnrolSignatureIO.Checked`, whose only constructor runs the
Ed25519 check of `mini-sig` over `miniFrame` and the SSHSIG check of `ssh-sig`
over `sshsigMessage` for exactly this memo.  `subjectTaken` is the authority
cell's answer for `subjectOf miniKey` (the receiver, P3b-2, reads it).

Time is the chain hour `tip.hour = tip.blockTime / 3600`, the unit of the public
enrollment view's `clock.hour` and `lease.expiresAt`.
-/
import Kernel.PayObservation

namespace Minidregg.Kernel.PayEnrolDecision

open Minidregg.Kernel.PayCell
open Minidregg.Kernel.PayTariff
open Minidregg.Kernel.PayEnrolMemo
open Minidregg.Kernel.PayObservation (Observation Credit decideObservation nullifierBytes)
open Minidregg.Theory.Store (Patch)

set_option autoImplicit false

/-- The part of the price that is not in the pay cell: the factory's birth
fee for the new account (`CreationTariff`, read by the receiver). -/
structure Price where
  birthFee : Nat
  deriving DecidableEq, Repr

/-- One node week plus the birth fee; derived, never stored (PAY §11.4). -/
def enrolPrice (tariff : Tariff) (price : Price) : Nat := price.birthFee + tariff.weekCredit

/-- The native verifier's two answers for the observation's memo. -/
structure Verified where
  mini : Bool
  ssh : Bool
  deriving DecidableEq, Repr

inductive Reject where
  | tariffInvalid
  | selfEnrolOff
  | notEnrolIndex
  | belowJournalFloor
  | observation (reason : PayObservation.Reject)
  deriving DecidableEq, Repr

structure EnrolPlan where
  memo : Memo
  /-- The enrollment float `A_enrol` (the enrollment index's assignee). -/
  float : Nat
  credit : Nat
  weeks : Nat
  /-- The next free book index for the new account, when one is installed. -/
  index : Option Nat
  leaseUntil : Nat
  deriving DecidableEq, Repr

structure RenewPlan where
  memo : Memo
  float : Nat
  account : Nat
  credit : Nat
  weeks : Nat
  leaseFrom : Nat
  leaseUntil : Nat
  deriving DecidableEq, Repr

inductive Decision where
  | enrol (plan : EnrolPlan)
  | renew (plan : RenewPlan)
  | journal (reason : JournalReason)
  deriving DecidableEq, Repr

def enrolPlan (store : PayStore) (tariff : Tariff) (price : Price) (tip : ChainTip) (memo : Memo)
    (float credit : Nat) : EnrolPlan :=
  let weeks := (credit - price.birthFee) / tariff.weekCredit
  ⟨memo, float, credit, weeks,
    if nextFree store < bookSize store then some (nextFree store) else none,
    tip.hour + 168 * weeks⟩

def renewPlan (tariff : Tariff) (tip : ChainTip) (memo : Memo) (record : EnrolRecord)
    (float credit : Nat) : RenewPlan :=
  let weeks := credit / tariff.weekCredit
  let leaseFrom := max (tip.hour) record.leaseUntil
  ⟨memo, float, record.account, credit, weeks, leaseFrom, leaseFrom + 168 * weeks⟩

/-- The decision on a parsed memo whose signatures have been checked. -/
def classifyMemo (store : PayStore) (tariff : Tariff) (price : Price) (tip : ChainTip)
    (float credit : Nat) (memo : Memo) (verified : Verified) (subjectTaken : Bool) : Decision :=
  if verified.mini = false then .journal .miniSigInvalid
  else if verified.ssh = false then .journal .sshSigInvalid
  else
    match enrolmentAt store memo.miniKey with
    | some record =>
        if record.sshBlob = memo.sshBlob then .renew (renewPlan tariff tip memo record float credit)
        else .journal .sshKeyMismatch
    | none =>
        if (sshIndexAt store memo.sshBlob).isSome then .journal .sshKeyTaken
        else if subjectTaken then .journal .subjectTaken
        else if credit < enrolPrice tariff price then .journal .belowPrice
        else .enrol (enrolPlan store tariff price tip memo float credit)

def classify (store : PayStore) (tariff : Tariff) (price : Price) (tip : ChainTip)
    (float credit : Nat) (field : MemoField) (verified : Verified) (subjectTaken : Bool) :
    Decision :=
  match field with
  | .absent => .journal .memoMissing
  | .unbound => .journal .memoUnbound
  | .invalid => .journal .memoInvalid
  | .present bytes =>
      match parse bytes with
      | .error refusal => .journal (.memoMalformed refusal)
      | .ok memo => classifyMemo store tariff price tip float credit memo verified subjectTaken

/-- The whole decision on one enrollment-index observation. -/
def decideEnrol (store : PayStore) (price : Price) (tip : ChainTip) (o : Observation)
    (verified : Verified) (subjectTaken : Bool) : Except Reject Decision :=
  match tariffOf store with
  | none => .error .tariffInvalid
  | some tariff =>
      if tariff.valid then
        match tariff.enrolIndex with
        | none => .error .selfEnrolOff
        | some index =>
            if o.index = index then
              if tariff.journalFloor ≤ o.amount then
                match decideObservation store tariff tip o with
                | .error reason => .error (.observation reason)
                | .ok credit =>
                    .ok (classify store tariff price tip credit.payer credit.credit o.memo verified
                      subjectTaken)
              else .error .belowJournalFloor
            else .error .notEnrolIndex
      else .error .tariffInvalid

/-! ## The pay-cell writes of each branch (the clock and the Book are the receiver's) -/

def EnrolPlan.patch (plan : EnrolPlan) (account : Nat) (slot : Nat) : Patch layout :=
  [.allocate .enrolment plan.memo.miniKey ⟨plan.memo.sshBlob, account, plan.index, plan.leaseUntil, slot⟩,
    .allocate .sshIndex plan.memo.sshBlob plan.memo.miniKey] ++
  match plan.index with
  | some index => [.allocate .assignment index account]
  | none => []

def RenewPlan.patch (plan : RenewPlan) (record : EnrolRecord) : Patch layout :=
  [.write .enrolment plan.memo.miniKey record { record with leaseUntil := plan.leaseUntil }]

def journalPatch (o : Observation) (reason : JournalReason) : Patch layout :=
  [.allocate .journal (nullifierBytes o) ⟨o.index, o.amount, o.slot, reason, o.memo⟩]

/-! ## What an accepted decision says -/

theorem decideEnrol_ok {store : PayStore} {price : Price} {tip : ChainTip} {o : Observation}
    {verified : Verified} {subjectTaken : Bool} {decision : Decision}
    (accepted : decideEnrol store price tip o verified subjectTaken = .ok decision) :
    ∃ tariff credit, tariffOf store = some tariff ∧ tariff.valid ∧
      tariff.enrolIndex = some o.index ∧ tariff.journalFloor ≤ o.amount ∧
      decideObservation store tariff tip o = .ok credit ∧
      decision = classify store tariff price tip credit.payer credit.credit o.memo verified
        subjectTaken := by
  unfold decideEnrol at accepted
  split at accepted
  · cases accepted
  next tariff present =>
    split at accepted
    next valid =>
      split at accepted
      · cases accepted
      next index enrol =>
        split at accepted
        next same =>
          split at accepted
          next floor =>
            split at accepted
            · cases accepted
            next credit observed =>
              cases accepted
              exact ⟨tariff, credit, present, valid, same ▸ enrol, floor, observed, rfl⟩
          · cases accepted
        · cases accepted
    · cases accepted

theorem classify_enrol {store : PayStore} {tariff : Tariff} {price : Price} {tip : ChainTip}
    {float credit : Nat} {field : MemoField} {verified : Verified} {subjectTaken : Bool}
    {plan : EnrolPlan}
    (accepted : classify store tariff price tip float credit field verified subjectTaken = .enrol plan) :
    ∃ bytes, field = .present bytes ∧ parse bytes = .ok plan.memo ∧
      verified.mini = true ∧ verified.ssh = true ∧
      enrolmentAt store plan.memo.miniKey = none ∧ sshIndexAt store plan.memo.sshBlob = none ∧
      subjectTaken = false ∧ enrolPrice tariff price ≤ credit ∧
      plan = enrolPlan store tariff price tip plan.memo float credit := by
  cases field with
  | absent => simp [classify] at accepted
  | unbound => simp [classify] at accepted
  | invalid => simp [classify] at accepted
  | present bytes =>
    cases parsed : parse bytes with
    | error refusal => simp [classify, parsed] at accepted
    | ok memo =>
      simp only [classify, parsed, classifyMemo] at accepted
      cases mini : verified.mini <;> simp only [mini, if_true, reduceCtorEq] at accepted
      cases ssh : verified.ssh <;> simp only [ssh, if_true, reduceCtorEq, Bool.true_eq_false,
        if_false] at accepted
      cases present : enrolmentAt store memo.miniKey with
      | some record =>
          simp only [present] at accepted
          split at accepted <;> cases accepted
      | none =>
          simp only [present] at accepted
          cases taken : sshIndexAt store memo.sshBlob with
          | some other => simp [taken] at accepted
          | none =>
            cases subject : subjectTaken with
            | true => simp [taken, subject] at accepted
            | false =>
              by_cases below : credit < enrolPrice tariff price
              · simp [taken, subject, below] at accepted
              · simp only [taken, subject, below, Option.isSome_none, Bool.false_eq_true, if_false,
                  Decision.enrol.injEq] at accepted
                subst accepted
                exact ⟨bytes, rfl, parsed, rfl, rfl, present, taken, rfl, by omega, rfl⟩

theorem classify_renew {store : PayStore} {tariff : Tariff} {price : Price} {tip : ChainTip}
    {float credit : Nat} {field : MemoField} {verified : Verified} {subjectTaken : Bool}
    {plan : RenewPlan}
    (accepted : classify store tariff price tip float credit field verified subjectTaken = .renew plan) :
    ∃ bytes record, field = .present bytes ∧ parse bytes = .ok plan.memo ∧
      verified.mini = true ∧ verified.ssh = true ∧
      enrolmentAt store plan.memo.miniKey = some record ∧ record.sshBlob = plan.memo.sshBlob ∧
      plan = renewPlan tariff tip plan.memo record float credit := by
  cases field with
  | absent => simp [classify] at accepted
  | unbound => simp [classify] at accepted
  | invalid => simp [classify] at accepted
  | present bytes =>
    cases parsed : parse bytes with
    | error refusal => simp [classify, parsed] at accepted
    | ok memo =>
      simp only [classify, parsed, classifyMemo] at accepted
      cases mini : verified.mini <;> simp only [mini, if_true, reduceCtorEq] at accepted
      cases ssh : verified.ssh <;> simp only [ssh, if_true, reduceCtorEq, Bool.true_eq_false,
        if_false] at accepted
      cases present : enrolmentAt store memo.miniKey with
      | some record =>
          simp only [present] at accepted
          by_cases same : record.sshBlob = memo.sshBlob
          · simp only [same, if_true, Decision.renew.injEq] at accepted
            subst accepted
            exact ⟨bytes, record, rfl, parsed, rfl, rfl, present, same, rfl⟩
          · simp [same] at accepted
      | none =>
          simp only [present] at accepted
          split at accepted
          · cases accepted
          · split at accepted
            · cases accepted
            · split at accepted <;> cases accepted

/-! ## The named theorems (PAY §11.4) -/

/-- **An enrollment is paid for**: the payment's credit covers the birth fee
and one node week. -/
theorem self_enroll_requires_fee {store : PayStore} {price : Price} {tip : ChainTip}
    {o : Observation} {verified : Verified} {subjectTaken : Bool} {plan : EnrolPlan}
    (accepted : decideEnrol store price tip o verified subjectTaken = .ok (.enrol plan)) :
    ∃ tariff, tariffOf store = some tariff ∧ plan.credit = tariff.creditFor o.amount ∧
      enrolPrice tariff price ≤ tariff.creditFor o.amount := by
  obtain ⟨tariff, credit, present, _, _, _, observed, decided⟩ := decideEnrol_ok accepted
  obtain ⟨_, _, _, _, _, _, _, _, _, exact⟩ := PayObservation.decideObservation_ok observed
  obtain ⟨_, _, _, _, _, _, _, _, enough, planned⟩ := classify_enrol decided.symm
  refine ⟨tariff, present, ?_, ?_⟩
  · rw [planned]; simp [enrolPlan]; rw [exact]
  · rw [exact] at enough; exact enough

/-- Below the price nothing is enrolled (it is renewed or journaled). -/
theorem below_price_never_enrols {store : PayStore} {price : Price} {tip : ChainTip}
    {o : Observation} {verified : Verified} {subjectTaken : Bool} {tariff : Tariff}
    (present : tariffOf store = some tariff) (below : tariff.creditFor o.amount < enrolPrice tariff price)
    (plan : EnrolPlan) : decideEnrol store price tip o verified subjectTaken ≠ .ok (.enrol plan) := by
  intro accepted
  obtain ⟨tariff', present', _, enough⟩ := self_enroll_requires_fee accepted
  rw [present] at present'
  simp only [Option.some.injEq] at present'
  subst present'
  omega

/-- **Once per key**: an enrolled Mini key is never enrolled again (the same
memo renews it; another ssh key is journaled `sshKeyMismatch`). -/
theorem self_enroll_once_per_key {store : PayStore} {price : Price} {tip : ChainTip}
    {o : Observation} {verified : Verified} {subjectTaken : Bool} {bytes : List UInt8} {memo : Memo}
    (carried : o.memo = .present bytes) (parsed : parse bytes = .ok memo)
    (enrolled : (enrolmentAt store memo.miniKey).isSome) (plan : EnrolPlan) :
    decideEnrol store price tip o verified subjectTaken ≠ .ok (.enrol plan) := by
  intro accepted
  obtain ⟨_, _, _, _, _, _, _, decided⟩ := decideEnrol_ok accepted
  obtain ⟨bytes', field, parsed', _, _, fresh, _⟩ := classify_enrol decided.symm
  rw [carried] at field
  cases field
  rw [parsed] at parsed'
  cases parsed'
  rw [fresh] at enrolled
  cases enrolled

/-- **An ssh key belongs to one Mini key**: a memo whose ssh key is indexed is
never a fresh enrollment (a squat is journaled `sshKeyTaken`). -/
theorem ssh_key_unique {store : PayStore} {price : Price} {tip : ChainTip}
    {o : Observation} {verified : Verified} {subjectTaken : Bool} {bytes : List UInt8} {memo : Memo}
    (carried : o.memo = .present bytes) (parsed : parse bytes = .ok memo)
    (taken : (sshIndexAt store memo.sshBlob).isSome) (plan : EnrolPlan) :
    decideEnrol store price tip o verified subjectTaken ≠ .ok (.enrol plan) := by
  intro accepted
  obtain ⟨_, _, _, _, _, _, _, decided⟩ := decideEnrol_ok accepted
  obtain ⟨bytes', field, parsed', _, _, _, free, _⟩ := classify_enrol decided.symm
  rw [carried] at field
  cases field
  rw [parsed] at parsed'
  cases parsed'
  rw [free] at taken
  cases taken

/-- **Both possessions**: an enrollment or a renewal needs the Mini key's and
the ssh key's signatures verified, over the memo the payment carried. -/
theorem enrol_requires_both_possessions {store : PayStore} {price : Price} {tip : ChainTip}
    {o : Observation} {verified : Verified} {subjectTaken : Bool} {memo : Memo}
    (accepted : (∃ plan : EnrolPlan, plan.memo = memo ∧
        decideEnrol store price tip o verified subjectTaken = .ok (.enrol plan)) ∨
      (∃ plan : RenewPlan, plan.memo = memo ∧
        decideEnrol store price tip o verified subjectTaken = .ok (.renew plan))) :
    ∃ bytes, o.memo = .present bytes ∧ parse bytes = .ok memo ∧
      verified.mini = true ∧ verified.ssh = true := by
  rcases accepted with ⟨plan, named, accepted⟩ | ⟨plan, named, accepted⟩
  · obtain ⟨_, _, _, _, _, _, _, decided⟩ := decideEnrol_ok accepted
    obtain ⟨bytes, field, parsed, mini, ssh, _⟩ := classify_enrol decided.symm
    exact ⟨bytes, field, named ▸ parsed, mini, ssh⟩
  · obtain ⟨_, _, _, _, _, _, _, decided⟩ := decideEnrol_ok accepted
    obtain ⟨bytes, _, field, parsed, mini, ssh, _⟩ := classify_renew decided.symm
    exact ⟨bytes, field, named ▸ parsed, mini, ssh⟩

/-- **A renewal never shortens a lease**: it runs from the later of now and
the current expiry, and the account renewed is the enrolled one. -/
theorem renew_extends_lease_never_shortens {store : PayStore} {price : Price} {tip : ChainTip}
    {o : Observation} {verified : Verified} {subjectTaken : Bool} {plan : RenewPlan}
    (accepted : decideEnrol store price tip o verified subjectTaken = .ok (.renew plan)) :
    ∃ record, enrolmentAt store plan.memo.miniKey = some record ∧
      record.sshBlob = plan.memo.sshBlob ∧ plan.account = record.account ∧
      record.leaseUntil ≤ plan.leaseUntil ∧ tip.hour ≤ plan.leaseUntil ∧
      plan.leaseUntil = plan.leaseFrom + 168 * plan.weeks := by
  obtain ⟨_, _, _, _, _, _, _, decided⟩ := decideEnrol_ok accepted
  obtain ⟨_, record, _, _, _, _, present, same, planned⟩ := classify_renew decided.symm
  refine ⟨record, present, same, ?_, ?_, ?_, ?_⟩
  · rw [planned]; rfl
  · rw [planned]; simp only [renewPlan]; omega
  · rw [planned]; simp only [renewPlan]; omega
  · rw [planned]; rfl

/-- **An enrollment buys at least one week**, starting now. -/
theorem enrol_lease_at_least_a_week {store : PayStore} {price : Price} {tip : ChainTip}
    {o : Observation} {verified : Verified} {subjectTaken : Bool} {plan : EnrolPlan}
    (accepted : decideEnrol store price tip o verified subjectTaken = .ok (.enrol plan)) :
    1 ≤ plan.weeks ∧ plan.leaseUntil = tip.hour + 168 * plan.weeks := by
  obtain ⟨tariff, credit, _, valid, _, _, _, decided⟩ := decideEnrol_ok accepted
  obtain ⟨_, _, _, _, _, _, _, _, enough, planned⟩ := classify_enrol decided.symm
  have positive : 0 < tariff.weekCredit := by
    unfold Tariff.weekCredit; have := valid.2.2.2.2.2.2.2; omega
  rw [planned]
  refine ⟨?_, rfl⟩
  simp only [enrolPlan]
  unfold enrolPrice at enough
  exact (Nat.le_div_iff_mul_le positive).mpr (by omega)

/-- **The decision does not depend on which transaction carried the memo**:
a replay of a published memo in a new transaction is decided exactly as the
original (so it renews its owner, a gift; PAY §11.3).  The transaction
identity only enters through the nullifier, which the durable preflight
spends once. -/
theorem decide_deterministic (store : PayStore) (price : Price) (tip : ChainTip) (o : Observation)
    (verified : Verified) (subjectTaken : Bool) (signature : List UInt8)
    (sameShape : signature.length = o.signature.length) :
    decideEnrol store price tip { o with signature := signature } verified subjectTaken =
      decideEnrol store price tip o verified subjectTaken := by
  unfold decideEnrol decideObservation
  simp only [sameShape]

/-- The journal branch writes one journal row and nothing else in the pay cell. -/
theorem journal_patch_footprint (o : Observation) (reason : JournalReason) :
    Patch.writeFootprint (journalPatch o reason) = {journalAddress (nullifierBytes o)} := by
  simp [journalPatch, Patch.writeFootprint, journalAddress, Theory.Store.Op.writeAddress?,
    Theory.Store.Op.address]

/-! ## Poles on a concrete pay cell

Book row 0 is the enrollment address (P1's happy-vector address, owned by the
float account 107); rows 1 and 2 are free deposit addresses.  The tariff turns
self-enrollment on at index 0 with the P1 mint, rate 1, a 10¹⁰ cap, node rate
5 952 380 and a 1-token journal floor; the birth fee is 9.  The clock is at
hour 500 000. -/

def enrolFixtureTariff : Tariff :=
  ⟨2, 0, fixtureMint, List.replicate 32 9, 6, 1, 10000000000, 1500, 5952380, some 0, 1000000⟩

def fixtureStore : PayStore :=
  ((((genesisStore.set tariffAddress (some enrolFixtureTariff)).set (bookAddress 0)
    (some fixtureAddress)).set (bookAddress 1) (some (List.replicate 32 1))).set (bookAddress 2)
    (some (List.replicate 32 2))).set (assignmentAddress 0) (some (107 : Nat))

def fixturePrice : Price := ⟨9⟩

def fixtureTip : ChainTip := ⟨1000, 1800000000⟩

/-- A payment of `amount` atomic units carrying `memo` to the enrollment index. -/
def paid (amount : Nat) (memo : MemoField) : Observation :=
  ⟨0, fixtureAddress, List.replicate 64 5, 900, 1799999000, amount, fixtureMint,
    List.replicate 32 9, memo⟩

def both : Verified := ⟨true, true⟩

/-- One node week and the birth fee: 999 999 849 credit = atomic units at rate 1. -/
theorem fixture_price : enrolPrice enrolFixtureTariff fixturePrice = 999999849 := by decide

def enrolled : PayStore :=
  (fixtureStore.set (enrolmentAddress fixtureMemo.miniKey)
    (some ⟨fixtureMemo.sshBlob, 150, some 1, 500100, 800⟩)).set
    (sshIndexAddress fixtureMemo.sshBlob) (some fixtureMemo.miniKey)

/-- Satisfiable pole: the real memo with enough credit enrolls, for one week
from hour 500 000, at the next free index 1. -/
theorem fixture_enrols :
    decideEnrol fixtureStore fixturePrice fixtureTip (paid 1000000000 (.present fixtureBytes)) both
      false = .ok (.enrol ⟨fixtureMemo, 107, 1000000000, 1, some 1, 500168⟩) := by decide +kernel

/-- Satisfiable pole: the same memo again renews, from the current expiry
(500 100 < now? no: now is 500 000, so from 500 100), by two weeks. -/
theorem fixture_renews :
    decideEnrol enrolled fixturePrice fixtureTip (paid 2000000000 (.present fixtureBytes)) both
      false = .ok (.renew ⟨fixtureMemo, 107, 150, 2000000000, 2, 500100, 500436⟩) := by
  decide +kernel

/-- A renewal below one week keeps the credit and the lease. -/
theorem small_renewal_keeps_lease :
    decideEnrol enrolled fixturePrice fixtureTip (paid 5000000 (.present fixtureBytes)) both
      false = .ok (.renew ⟨fixtureMemo, 107, 150, 5000000, 0, 500100, 500100⟩) := by
  decide +kernel

theorem memo_missing_journaled :
    decideEnrol fixtureStore fixturePrice fixtureTip (paid 1000000000 .absent) both false =
      .ok (.journal .memoMissing) := by decide +kernel

theorem memo_unbound_journaled :
    decideEnrol fixtureStore fixturePrice fixtureTip (paid 1000000000 .unbound) both false =
      .ok (.journal .memoUnbound) := by decide +kernel

theorem memo_invalid_journaled :
    decideEnrol fixtureStore fixturePrice fixtureTip (paid 1000000000 .invalid) both false =
      .ok (.journal .memoInvalid) := by decide +kernel

theorem memo_malformed_journaled :
    decideEnrol fixtureStore fixturePrice fixtureTip
      (paid 1000000000 (.present (mutate 7 50 fixtureBytes))) both false =
      .ok (.journal (.memoMalformed .version)) := by decide +kernel

theorem mini_sig_invalid_journaled :
    decideEnrol fixtureStore fixturePrice fixtureTip (paid 1000000000 (.present fixtureBytes))
      ⟨false, true⟩ false = .ok (.journal .miniSigInvalid) := by decide +kernel

theorem ssh_sig_invalid_journaled :
    decideEnrol fixtureStore fixturePrice fixtureTip (paid 1000000000 (.present fixtureBytes))
      ⟨true, false⟩ false = .ok (.journal .sshSigInvalid) := by decide +kernel

theorem below_price_journaled :
    decideEnrol fixtureStore fixturePrice fixtureTip (paid 999999848 (.present fixtureBytes)) both
      false = .ok (.journal .belowPrice) := by decide +kernel

/-- At exactly the price the key enrolls (the other pole of `below_price_journaled`). -/
theorem at_price_enrols :
    decideEnrol fixtureStore fixturePrice fixtureTip (paid 999999849 (.present fixtureBytes)) both
      false = .ok (.enrol ⟨fixtureMemo, 107, 999999849, 1, some 1, 500168⟩) := by decide +kernel

/-- A squat: another Mini key's memo naming an ssh key already enrolled. -/
theorem ssh_key_taken_journaled :
    decideEnrol (fixtureStore.set (sshIndexAddress fixtureMemo.sshBlob) (some (List.replicate 32 3)))
      fixturePrice fixtureTip (paid 1000000000 (.present fixtureBytes)) both false =
      .ok (.journal .sshKeyTaken) := by decide +kernel

theorem ssh_key_mismatch_journaled :
    decideEnrol (fixtureStore.set (enrolmentAddress fixtureMemo.miniKey)
        (some ⟨sshBlobOf (List.replicate 32 4), 150, some 1, 500100, 800⟩))
      fixturePrice fixtureTip (paid 1000000000 (.present fixtureBytes)) both false =
      .ok (.journal .sshKeyMismatch) := by decide +kernel

theorem subject_taken_journaled :
    decideEnrol fixtureStore fixturePrice fixtureTip (paid 1000000000 (.present fixtureBytes)) both
      true = .ok (.journal .subjectTaken) := by decide +kernel

/-- Refusing poles: nothing is decided (nor consumed). -/
theorem self_enrol_off_refused :
    decideEnrol (fixtureStore.set tariffAddress (some { enrolFixtureTariff with enrolIndex := none }))
      fixturePrice fixtureTip (paid 1000000000 (.present fixtureBytes)) both false =
      .error .selfEnrolOff := by decide +kernel

theorem ordinary_index_refused :
    decideEnrol fixtureStore fixturePrice fixtureTip
      { paid 1000000000 (.present fixtureBytes) with index := 1 } both false =
      .error .notEnrolIndex := by decide +kernel

theorem below_floor_refused :
    decideEnrol fixtureStore fixturePrice fixtureTip (paid 999999 (.present fixtureBytes)) both
      false = .error .belowJournalFloor := by decide +kernel

theorem wrong_mint_refused :
    decideEnrol fixtureStore fixturePrice fixtureTip
      { paid 1000000000 (.present fixtureBytes) with mint := List.replicate 32 8 } both false =
      .error (.observation .wrongMint) := by decide +kernel

#assert_axioms decideEnrol_ok
#assert_axioms classify_enrol
#assert_axioms classify_renew
#assert_axioms self_enroll_requires_fee
#assert_axioms below_price_never_enrols
#assert_axioms self_enroll_once_per_key
#assert_axioms ssh_key_unique
#assert_axioms enrol_requires_both_possessions
#assert_axioms renew_extends_lease_never_shortens
#assert_axioms enrol_lease_at_least_a_week
#assert_axioms decide_deterministic
#assert_axioms journal_patch_footprint
#assert_axioms fixture_price
#assert_axioms fixture_enrols
#assert_axioms fixture_renews
#assert_axioms small_renewal_keeps_lease
#assert_axioms memo_missing_journaled
#assert_axioms memo_unbound_journaled
#assert_axioms memo_invalid_journaled
#assert_axioms memo_malformed_journaled
#assert_axioms mini_sig_invalid_journaled
#assert_axioms ssh_sig_invalid_journaled
#assert_axioms below_price_journaled
#assert_axioms at_price_enrols
#assert_axioms ssh_key_taken_journaled
#assert_axioms ssh_key_mismatch_journaled
#assert_axioms subject_taken_journaled
#assert_axioms self_enrol_off_refused
#assert_axioms ordinary_index_refused
#assert_axioms below_floor_refused
#assert_axioms wrong_mint_refused

end Minidregg.Kernel.PayEnrolDecision
